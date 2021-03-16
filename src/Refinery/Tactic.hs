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
  , gather
  , pruning
  , ensure
  -- * Errors and Error Handling
  , failure
  , handler
  , handler_
  -- * Extract Manipulation
  , tweak
  , peek
  , poke
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
  ) where

import Data.Bifunctor
import qualified Data.Monoid as Mon

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State.Strict

import Refinery.ProofState
import Refinery.Tactic.Internal

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

-- | @gather t f@ runs the tactic @t@, then runs @f@ with all of the generated subgoals to determine
-- the next tactic to run.
gather :: (MonadExtract ext err m) => TacticT jdg ext err s m a -> ([(a, jdg)] -> TacticT jdg ext err s m a) -> TacticT jdg ext err s m a
gather t f = tactic $ \j -> do
    s <- get
    results <- lift $ proofs s $ proofState t j
    case results of
      Left errs -> Mon.getAlt $ foldMap (\err -> Mon.Alt $ Failure err Axiom) errs
      Right pfs -> Mon.getAlt $ foldMap (\(Proof _ _ jdgs) -> Mon.Alt $ proofState (f jdgs) j) pfs

-- | @pruning t f@ runs the tactic @t@, and then applies a predicate to all of the generated subgoals.
pruning
    :: (MonadExtract ext err m)
    => TacticT jdg ext err s m ()
    -> ([jdg] -> Maybe err)
    -> TacticT jdg ext err s m ()
pruning t p = gather t $ maybe t failure . p . fmap snd

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

-- | @peek t k@ lets us examine the extract produced by @t@, and then run a tactic based off it's value.
peek :: (Functor m) => TacticT jdg ext err s m a -> (ext -> TacticT jdg ext err s m b) -> TacticT jdg ext err s m a
peek t k = (tactic $ \j -> Subgoal ((), j) (\e -> fmap (first (const ())) $ proofState (k e) j)) >> t

-- | @poke t k@ lets us examine the extract produced by @t@, and then run a tactic that produces a new extract.
poke :: (Functor m) => TacticT jdg ext err s m () -> (ext -> TacticT jdg ext err s m ext) -> TacticT jdg ext err s m ()
poke t k = tactic $ \j -> Subgoal ((), j) $ \ext -> do
    (ext', j') <- proofState (k ext) j
    mapExtract id (const ext') $ proofState t j'

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
-- Note that this function will backtrack on errors. If you want a version that provides partial proofs,
-- use 'runPartialTacticT'
runTacticT :: (MonadExtract ext err m) => TacticT jdg ext err s m () -> jdg -> s -> m (Either [err] [(Proof s jdg ext)])
runTacticT t j s = proofs s $ fmap snd $ proofState t j

-- | Run a tactic, and get just the list of extracts, ignoring any other information.
evalTacticT :: (MonadExtract ext err m) => TacticT jdg ext err s m () -> jdg -> s -> m [ext]
evalTacticT t j s = either (const []) (map pf_extract) <$> runTacticT t j s

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
-- Note that this function will produce a so called "Partial Proof". This means that we no longer backtrack on errors,
-- but rather leave an unsolved hole, and continue synthesizing a extract.
-- If you want a version that backgracks on errors, see 'runTacticT'.
--
-- Note that this version is inherently slower than 'runTacticT', as it needs to continue producing extracts.
-- Furthermore, it will return all of the 'SuccessfulProof' before the 'PartialProof'.
runPartialTacticT :: (MonadExtract ext err m) => TacticT jdg ext err s m () -> jdg -> s -> m (Either [PartialProof s err jdg ext] [(Proof s jdg ext)])
runPartialTacticT t j s = partialProofs s $ fmap snd $ proofState t j

-- | Turn an inference rule that examines the current goal into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext err s m ext) -> TacticT jdg ext err s m ()
rule r = tactic $ \j -> fmap ((),) $ unRuleT (r j)

-- | Turn an inference rule into a tactic.
rule_ :: (Monad m) => RuleT jdg ext err s m ext -> TacticT jdg ext err s m ()
rule_ r = tactic $ \_ -> fmap ((),) $ unRuleT r
