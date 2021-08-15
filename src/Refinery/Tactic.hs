{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
-----------------------------------------------------------------------------
-- | Tactics and Tactic Combinators
--
-- This module contains everything you need to start defining tactics
-- and tactic combinators.
-- Module      :  Refinery.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
module Refinery.Tactic
  ( TacticT
  , runTacticT
  , runStreamingTacticT
  , ListT(..)
  , Elem(..)
  , runPartialTacticT
  , evalTacticT
  , Proof(..)
  , PartialProof(..)
  -- * Tactic Combinators
  , (<@>)
  , (<%>)
  , try
  , commit
  , many_
  , some_
  , choice
  , progress
  , ensure
  -- * Errors and Error Handling
  , failure
  , handler
  , handler_
  -- * Extract Manipulation
  , tweak
  -- * Subgoal Manipulation
  , goal
  , inspect
  , focus
  -- * Tactic Creation
  , MonadExtract(..)
  , RuleT
  , rule
  , rule_
  , subgoal
  , unsolvable
  -- * Introspection
  , MetaSubst(..)
  , DependentMetaSubst(..)
  , reify
  , resume
  , resume'
  , pruning
  , peek
  , attempt
  , annotate
  ) where

import Control.Applicative
import Control.Monad.State.Class

import Data.Bifunctor

import Refinery.ProofState
import Refinery.Tactic.Internal
import Control.Monad.State.Strict (mapStateT)

-- | Create a tactic that applies each of the tactics in the list to one subgoal.
--
-- When the number of subgoals is greater than the number of provided tactics,
-- the identity tactic is applied to the remainder. When the number of subgoals is
-- less than the number of provided tactics, the remaining tactics are ignored.
(<@>) :: (Functor m) => TacticT jdg ext err s m a -> [TacticT jdg ext err s m a] -> TacticT jdg ext err s m a
t <@> ts = tactic $ \j -> subgoals (fmap (\t' (_,j') -> proofState t' j') ts) (proofState t j)

infixr 3 <%>

-- | @t1 <%> t2@ will interleave the execution of @t1@ and @t2@. This is useful if @t1@ will
-- produce an infinite number of extracts, as we will still run @t2@. This is contrasted with
-- @t1 <|> t2@, which will not ever consider @t2@ if @t1@ produces an infinite number of extracts.
(<%>) :: TacticT jdg ext err s m a -> TacticT jdg ext err s m a -> TacticT jdg ext err s m a
t1 <%> t2 = tactic $ \j -> Interleave (proofState t1 j) (proofState t2 j)

-- | Tries to run a tactic, backtracking on failure
try :: (Monad m) => TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
try t = t <|> pure ()


annotate :: String -> TacticT jdg ext err s m a -> TacticT jdg ext err s m a
annotate name = TacticT . mapStateT (Annotate name) . unTacticT

-- | @commit t1 t2@ will run @t1@, and then run @t2@ only if @t1@ (and all subsequent tactics) failed to produce any successes.
--
-- NOTE: @commit@ does have some sneaky semantics that you have to be aware of. Specifically, it interacts a bit
-- surprisingly with '>>='. Namely, the following algebraic law holds
-- @
--     commit t1 t2 >>= f = commit (t1 >>= f) (t2 >>= f)
-- @
-- For instance, if you have something like @commit t1 t2 >>= somethingThatMayFail@, then this
-- law implies that this is the same as @commit (t1 >>= somethingThatMayFail) (t2 >>= somethingThatMayFail)@,
-- which means that we might execute @t2@ _even if_ @t1@ seemingly succeeds.
commit :: TacticT jdg ext err s m a -> TacticT jdg ext err s m a -> TacticT jdg ext err s m a
commit t1 t2 = tactic $ \j -> Commit (proofState t1 j) (proofState t2 j)

-- | Runs a tactic 0 or more times until it fails.
-- Note that 'many_' is almost always the right choice over 'many'.
-- Due to the semantics of 'Alternative', 'many' will create a bunch
-- of partially solved goals along the way, one for each iteration.
many_ :: (Monad m) => TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
many_ t = try (t >> many_ t)

-- | Runs a tactic 1 or more times until it fails.
-- Note that 'some_' is almost always the right choice over 'some'.
-- Due to the semantics of 'Alternative', 'some' will create a bunch
-- of partially solved goals along the way, one for each iteration.
some_ :: (Monad m) => TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
some_ t = t >> many_ t

-- | Get the current goal
goal :: (Functor m) => TacticT jdg ext err s m jdg
goal = TacticT get

-- | Inspect the current goal.
inspect :: (Functor m) => (jdg -> a) -> TacticT jdg ext err s m a
inspect f = TacticT $ gets f

-- | @choice ts@ will run all of the tactics in the list against the current subgoals,
-- and interleave their extracts in a manner similar to '<%>'.
choice :: (Monad m) => [TacticT jdg ext err s m a] -> TacticT jdg ext err s m a
choice = foldr (<%>) empty

-- | @failure err@ will create an unsolvable hole that will be ignored by subsequent tactics.
failure :: err -> TacticT jdg ext err s m a
failure err = tactic $ \_ -> Failure err Axiom

-- | @handler f@ will install an "error handler". These let you add more context to errors, and
-- potentially run effects. For instance, you may want to take note that a particular situation is
-- unsolvable, and that we shouldn't attempt to run this series of tactics against a given goal again.
--
-- Note that handlers further down the stack get run before those higher up the stack.
-- For instance, consider the following example:
-- @
--     handler f >> handler g >> failure err
-- @
-- Here, @g@ will get run before @f@.
handler :: (err -> m err) -> TacticT jdg ext err s m ()
handler h = tactic $ \j -> Handle (Subgoal ((), j) Axiom) h

-- | A variant of 'handler' that doesn't modify the error at all, and solely exists to run effects.
handler_ :: (Functor m) => (err -> m ()) -> TacticT jdg ext err s m ()
handler_ h = handler (\err -> err <$ h err)

-- | @progress eq err t@ applies the tactic @t@, and checks to see if the
-- resulting subgoals are all equal to the initial goal by using @eq@. If they
-- are, it throws @err@.
progress :: (Monad m) => (jdg -> jdg -> Bool) -> err ->  TacticT jdg ext err s m a -> TacticT jdg ext err s m a
progress eq err t = do
  j <- goal
  a <- t
  j' <- goal
  if j `eq` j' then pure a else failure err

-- | @ensure p f t@ runs the tactic @t@, and applies a predicate to the state after the execution of @t@. We also run
-- a "cleanup" function @f@. Note that the predicate is applied to the state _before_ the cleanup function is run.
ensure :: (Monad m) => (s -> Maybe err) -> (s -> s) -> TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
ensure p f t = check >> t
    where
      -- NOTE It may seem backwards to run check _before_ t, but we
      -- need to do the predicate check after the subgoal has been resolved,
      -- and not on every generated subgoal.
      check = rule $ \j -> do
          e <- subgoal j
          s <- get
          modify f
          case p s of
            Just err -> unsolvable err
            Nothing -> pure e

-- | Apply the first tactic, and then apply the second tactic focused on the @n@th subgoal.
focus :: (Functor m) => TacticT jdg ext err s m () -> Int -> TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
focus t n t' = t <@> (replicate n (pure ()) ++ [t'] ++ repeat (pure ()))

-- | @tweak f t@ lets us modify the extract produced by the tactic @t@.
tweak :: (Functor m) => (ext -> ext) -> TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
tweak f t = tactic $ \j -> mapExtract id f $ proofState t j

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
-- Note that this function will backtrack on errors. If you want a version that provides partial proofs,
-- use 'runPartialTacticT'
runTacticT :: (MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> jdg -> s -> m (Either [err] [(Proof s meta jdg ext)])
runTacticT t j s = proofs s $ fmap snd $ proofState t j

runStreamingTacticT :: (MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> jdg -> s -> ListT m (Either err (Proof s meta jdg ext))
runStreamingTacticT t j s = streamProofs s $ fmap snd $ proofState t j

-- | Run a tactic, and get just the list of extracts, ignoring any other information.
evalTacticT :: (MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> jdg -> s -> m [ext]
evalTacticT t j s = either (const []) (map pf_extract) <$> runTacticT t j s

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
-- Note that this function will produce a so called "Partial Proof". This means that we no longer backtrack on errors,
-- but rather leave an unsolved hole, and continue synthesizing a extract.
-- If you want a version that backgracks on errors, see 'runTacticT'.
--
-- Note that this version is inherently slower than 'runTacticT', as it needs to continue producing extracts.
runPartialTacticT :: (MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> jdg -> s -> m (Either [PartialProof s err meta jdg ext] [(Proof s meta jdg ext)])
runPartialTacticT t j s = partialProofs s $ fmap snd $ proofState t j

-- | Turn an inference rule that examines the current goal into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext err s m ext) -> TacticT jdg ext err s m ()
rule r = tactic $ \j -> fmap ((),) $ unRuleT (r j)

-- | Turn an inference rule into a tactic.
rule_ :: (Monad m) => RuleT jdg ext err s m ext -> TacticT jdg ext err s m ()
rule_ r = tactic $ \_ -> fmap ((),) $ unRuleT r

introspect :: (MonadExtract meta ext err s m) => TacticT jdg ext err s m a -> (err -> TacticT jdg ext err s m ()) -> (Proof s meta jdg ext -> TacticT jdg ext err s m ()) -> TacticT jdg ext err s m ()
introspect t handle f = rule $ \j -> do
    s <- get
    (RuleT $ speculate s $ proofState_ t j) >>= \case
      Left err -> RuleT $ proofState_ (handle err) j
      Right pf -> RuleT $ proofState_ (f pf) j

-- | @reify t f@ will execute the tactic @t@, and resolve all of it's subgoals by filling them with holes.
-- The resulting subgoals and partial extract are then passed to @f@.
reify :: forall meta jdg ext err s m . (MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> (Proof s meta jdg ext -> TacticT jdg ext err s m ()) -> TacticT jdg ext err s m ()
reify t f = introspect t failure f

-- | @resume goals partial@ allows for resumption of execution after a call to 'reify'.
-- If your language doesn't support dependent subgoals, consider using @resume'@ instead.
resume :: forall meta jdg ext err s m. (DependentMetaSubst meta jdg ext, Monad m) => Proof s meta jdg ext -> TacticT jdg ext err s m ()
resume (Proof partialExt s goals) = rule $ \_ -> do
    put s
    solns <- dependentSubgoals goals
    pure $ foldr (\(meta, soln) ext -> substMeta meta soln ext) partialExt solns
    where
      dependentSubgoals :: [(meta, jdg)] -> RuleT jdg ext err s m [(meta, ext)]
      dependentSubgoals [] = pure []
      dependentSubgoals ((meta, g) : gs) = do
          soln <- subgoal g
          solns <- dependentSubgoals $ fmap (second (dependentSubst meta soln)) gs
          pure ((meta, soln) : solns)

-- | A version of @resume@ that doesn't perform substitution into the goal types.
-- This only makes sense if your language doesn't support dependent subgoals.
-- If it does, use @resume@ instead, as this will leave the dependent subgoals with holes in them.
resume' :: forall meta jdg ext err s m. (MetaSubst meta ext, Monad m) => Proof s meta jdg ext -> TacticT jdg ext err s m ()
resume' (Proof partialExt s goals) = rule $ \_ -> do
    put s
    solns <- traverse (\(meta, g) -> (meta, ) <$> subgoal g) goals
    pure $ foldr (\(meta, soln) ext -> substMeta meta soln ext) partialExt solns

-- | @pruning t p@ will execute @t@, and then apply @p@ to any subgoals it generates. If this predicate returns an error, we terminate the execution.
-- Otherwise, we resume execution via 'resume''.
pruning :: (MetaSubst meta ext, MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> ([jdg] -> Maybe err) -> TacticT jdg ext err s m ()
pruning t p = reify t $ \pf -> case (p $ fmap snd $ pf_unsolvedGoals pf) of
  Just err -> failure err
  Nothing ->  resume' pf

-- | @peek t p@ will execute @t@, and then apply @p@ to the extract it produces. If this predicate returns an error, we terminate the execution.
-- Otherwise, we resume execution via 'resume''.
--
-- Note that the extract produced may contain holes, as it is the extract produced by running _just_ @t@ against the current goal.
peek :: (MetaSubst meta ext, MonadExtract meta ext err s m) => TacticT jdg ext err s m () -> (ext -> Maybe err) -> TacticT jdg ext err s m ()
peek t p = reify t $ \pf -> case (p $ pf_extract pf) of
  Just err -> failure err
  Nothing ->  resume' pf

-- | @attempt t1 t2@ will partially execute @t1@, inspect it's result, and only run @t2@ if it fails.
-- If @t1@ succeeded, we will 'resume'' execution of it.
attempt :: (MonadExtract meta ext err s m, MetaSubst meta ext) => TacticT jdg ext err s m () -> TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
attempt t1 t2 = introspect t1 (\_ -> t2) resume'
