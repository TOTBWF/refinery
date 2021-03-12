{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Refinery.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
module Refinery.Tactic
  ( TacticT
  , runTacticT
  , runPartialTacticT
  , Proof(..)
  , PartialProof(..)
  -- * Tactic Combinators
  , (<@>)
  , (<%>)
  , try
  , many_
  , some_
  , choice
  , progress
  , gather
  , pruning
  , ensure
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

-- | @progress eq err t@ applies the tactic @t@, and checks to see if the
-- resulting subgoals are all equal to the initial goal by using @eq@. If they
-- are, it throws @err@.
progress :: (Monad m) => (jdg -> jdg -> Bool) -> err ->  TacticT jdg ext err s m a -> TacticT jdg ext err s m a
progress eq err t = do
  j <- goal
  a <- t
  j' <- goal
  if j `eq` j' then pure a else throwError err

-- | @gather t f@ runs the tactic @t@, then runs @f@ with all of the generated subgoals to determine
-- the next tactic to run.
-- FIXME: Partial Proofs ?????
gather :: (MonadExtract ext err m) => TacticT jdg ext err s m a -> ([(a, jdg)] -> TacticT jdg ext err s m a) -> TacticT jdg ext err s m a
gather t f = tactic $ \j -> do
    s <- get
    results <- lift $ proofs s $ proofState t j
    case results of
      Left errs -> msum $ fmap throwError errs
      Right pfs -> msum $ fmap (\(Proof _ _ jdgs) -> proofState (f jdgs) j) pfs

-- | @pruning t f@ runs the tactic @t@, and then applies a predicate to all of the generated subgoals.
pruning
    :: (MonadExtract ext err m)
    => TacticT jdg ext err s m ()
    -> ([jdg] -> Maybe err)
    -> TacticT jdg ext err s m ()
pruning t p = gather t $ maybe t throwError . p . fmap snd

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
tweak f t = tactic $ \j -> mapExtract' f $ proofState t j

-- | @peek t k@ lets us examine the extract produced by @t@, and then run a tactic based off it's value.
peek :: (Functor m) => TacticT jdg ext err s m a -> (ext -> TacticT jdg ext err s m b) -> TacticT jdg ext err s m a
peek t k = (tactic $ \j -> Subgoal ((), j) (\e -> fmap (first (const ())) $ proofState (k e) j)) >> t

-- | @poke t k@ lets us examine the extract produced by @t@, and then run a tactic that produces a new extract.
poke :: (Functor m) => TacticT jdg ext err s m () -> (ext -> TacticT jdg ext err s m ext) -> TacticT jdg ext err s m ()
poke t k = tactic $ \j -> Subgoal ((), j) $ \ext -> do
    (ext', j') <- proofState (k ext) j
    mapExtract' (const ext') $ proofState t j'

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
-- Note that this function will backtrack on errors. If you want a version that provides partial proofs,
-- use 'runPartialTacticT'
runTacticT :: (MonadExtract ext err m) => TacticT jdg ext err s m () -> jdg -> s -> m (Either [err] [(Proof ext s jdg)])
runTacticT t j s = proofs s $ fmap snd $ proofState t j

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
-- Note that this function will produce a so called "Partial Proof". This means that we no longer backtrack on errors,
-- but rather leave an unsolved hole, and continue synthesizing a extract.
-- If you want a version that backgracks on errors, see 'runTacticT'.
--
-- Note that this version is inherently slower than 'runTacticT', as it needs to continue producing extracts.
-- Furthermore, it will return all of the 'SuccessfulProof' before the 'PartialProof'.
runPartialTacticT :: (MonadExtract ext err m) => TacticT jdg ext err s m () -> jdg -> s -> m (Either [PartialProof ext s jdg err] [(Proof ext s jdg)])
runPartialTacticT t j s = partialProofs s $ fmap snd $ proofState t j

-- | Turn an inference rule that examines the current goal into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext err s m ext) -> TacticT jdg ext err s m ()
rule r = tactic $ \j -> fmap ((),) $ unRuleT (r j)

-- | Turn an inference rule into a tactic.
rule_ :: (Monad m) => RuleT jdg ext err s m ext -> TacticT jdg ext err s m ()
rule_ r = tactic $ \_ -> fmap ((),) $ unRuleT r
