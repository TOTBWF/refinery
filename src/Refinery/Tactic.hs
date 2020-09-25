{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
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
  -- * Tactic Combinators
  , (<@>)
  , try
  , many_
  , choice
  , progress
  , MonadLogic(..)
  -- * Subgoal Manipulation
  , goal
  , focus
  -- * Tactic Creation
  , MonadExtract(..)
  , MonadRule(..)
  , RuleT
  , rule
  , MonadProvable(..)
  , ProvableT(..)
  , Provable
  , runProvable
  ) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Logic

import Refinery.ProofState
import Refinery.Tactic.Internal


-- -- | Create a tactic that applies each of the tactics in the list to one subgoal.
-- --
-- -- When the number of subgoals is greater than the number of provided tactics,
-- -- the identity tactic is applied to the remainder. When the number of subgoals is
-- -- less than the number of provided tactics, the remaining tactics are ignored.
(<@>) :: (MonadProvable jdg m) => TacticT jdg ext err m a -> [TacticT jdg ext err m a] -> TacticT jdg ext err m a
t <@> ts = tactic $ \j -> subgoals (fmap (\t' (_,j') -> proofState t' j') ts) (proofState t j)

-- | Tries to run a tactic, backtracking on failure
try :: (MonadProvable jdg m) => TacticT jdg ext err m () -> TacticT jdg ext err m ()
try t = t <|> pure ()

-- | Runs a tactic repeatedly until it fails
many_ :: (MonadProvable jdg m) => TacticT jdg ext err m () -> TacticT jdg ext err m ()
many_ t = try (t >> many_ t)

-- | Get the current goal
goal :: (MonadProvable jdg m) => TacticT jdg ext err m jdg
goal = TacticT $ get

-- | @choice err ts@ tries to apply a series of tactics @ts@, and commits to the
-- 1st tactic that succeeds. If they all fail, then @err@ is thrown
choice :: (MonadProvable jdg m) => [TacticT jdg ext err m a] -> TacticT jdg ext err m a
choice [] = empty
choice (t:ts) = t `interleave` choice ts

-- -- | @progress eq err t@ applies the tactic @t@, and checks to see if the
-- -- resulting subgoals are all equal to the initial goal by using @eq@. If they
-- -- are, it throws @err@.
progress :: (MonadProvable jdg m) => (jdg -> jdg -> Bool) -> err ->  TacticT jdg ext err m a -> TacticT jdg ext err m a
progress eq err t = do
  j <- goal
  a <- t
  j' <- goal
  if j `eq` j' then pure a else throwError err

-- -- | Apply the first tactic, and then apply the second tactic focused on the @n@th subgoal.
focus :: (MonadProvable jdg m) => TacticT jdg ext err m () -> Int -> TacticT jdg ext err m () -> TacticT jdg ext err m ()
focus t n t' = t <@> (replicate n (pure ()) ++ [t'] ++ repeat (pure ()))

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
runTacticT :: (MonadExtract ext m) => TacticT jdg ext err m () -> jdg -> m [Either err (ext, [jdg])]
runTacticT t j = proofs $ fmap snd $ proofState t j

-- | Turn an inference rule into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext err m ext) -> TacticT jdg ext err m ()
rule r = tactic $ \j -> fmap ((),) $ unRuleT (r j)

