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
  -- * Tactic Combinators
  , (<@>)
  , (<%>)
  , commit
  , try
  , many_
  , choice
  , progress
  , gather
  , pruning
  , ensure
  , peek
  -- * Subgoal Manipulation
  , goal
  , focus
  -- * Tactic Creation
  , MonadExtract(..)
  , MonadRule(..)
  , RuleT
  , rule
  ) where

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

-- | @commit t1 t2@ will run @t1@, and then only run @t2@ if @t1@ failed to produce any extracts.
commit :: TacticT jdg ext err s m a -> TacticT jdg ext err s m a -> TacticT jdg ext err s m a
commit t1 t2 = tactic $ \j -> Commit (proofState t1 j) (proofState t2 j)

-- | Tries to run a tactic, backtracking on failure
try :: (Monad m) => TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
try t = t <|> pure ()

-- | Runs a tactic repeatedly until it fails
many_ :: (Monad m) => TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
many_ t = try (t >> many_ t)

-- | Get the current goal
goal :: (Functor m) => TacticT jdg ext err s m jdg
goal = TacticT $ get

-- | @choice ts@ will run all of the tactics in the list against the current subgoals,
-- and interleave their extracts in a manner similar to '<%>'.
choice :: (Monad m) => [TacticT jdg ext err s m a] -> TacticT jdg ext err s m a
choice [] = empty
choice (t:ts) = t <%> choice ts

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
gather :: (MonadExtract ext m) => TacticT jdg ext err s m a -> ([(a, jdg)] -> TacticT jdg ext err s m a) -> TacticT jdg ext err s m a
gather t f = tactic $ \j -> do
    s <- get
    results <- lift $ proofs s $ proofState t j
    msum $ flip fmap results $ \case
        Left err -> throwError err
        Right (_, _, jdgs) -> proofState (f jdgs) j

-- | @pruning t f@ runs the tactic @t@, and then applies a predicate to all of the generated subgoals.
pruning
    :: (MonadExtract ext m)
    => TacticT jdg ext err s m ()
    -> ([jdg] -> Maybe err)
    -> TacticT jdg ext err s m ()
pruning t p = gather t $ maybe t throwError . p . fmap snd

-- | @filterT p f t@ runs the tactic @t@, and applies a predicate to the state after the execution of @t@. We also run
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
            Just err -> throwError err
            Nothing -> pure e

-- | Apply the first tactic, and then apply the second tactic focused on the @n@th subgoal.
focus :: (Functor m) => TacticT jdg ext err s m () -> Int -> TacticT jdg ext err s m () -> TacticT jdg ext err s m ()
focus t n t' = t <@> (replicate n (pure ()) ++ [t'] ++ repeat (pure ()))

-- | @peek t k@ lets us examine the extract produced by @t@, and then run a tactic based off it's value.
peek :: (Functor m) => TacticT jdg ext err s m a -> (ext -> TacticT jdg ext err s m b) -> TacticT jdg ext err s m a
peek t k = (tactic $ \j -> Subgoal () (\e -> void $ proofState (k e) j)) >> t

-- | Runs a tactic, producing a list of possible extracts, along with a list of unsolved subgoals.
runTacticT :: (MonadExtract ext m) => TacticT jdg ext err s m () -> jdg -> s -> m [Either err (ext, s, [jdg])]
runTacticT t j s = proofs s $ fmap snd $ proofState t j

-- | Turn an inference rule into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext err s m ext) -> TacticT jdg ext err s m ()
rule r = tactic $ \j -> fmap ((),) $ unRuleT (r j)

