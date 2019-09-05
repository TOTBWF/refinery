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
  -- * Subgoal Manipulation
  , goal
  , focus
  , forSubgoals
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
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans
import Control.Monad.IO.Class
import Control.Monad.Logic.Class
import Control.Monad.Morph

import Data.Bifunctor

import Pipes.Core
import Pipes.Lift (runStateP)

import Refinery.ProofState
import Refinery.Tactic.Internal

-- | Create a tactic that applies each of the tactics in the list to one subgoal.
--
-- When the number of subgoals is greater than the number of provided tactics,
-- the identity tactic is applied to the remainder. When the number of subgoals is
-- less than the number of provided tactics, the remaining tactics are ignored.
(<@>) :: (MonadProvable jdg m) => TacticT jdg ext m () -> [TacticT jdg ext m ()] -> TacticT jdg ext m ()
t <@> ts = stateful t applyTac (ts ++ repeat (pure ()))
  where
    applyTac j = do
      tac <- gets head
      modify tail
      hoist lift $ asRule j tac

-- | Tries to run a tactic, backtracking on failure
try :: (MonadProvable jdg m, MonadLogic m) => TacticT jdg ext m () -> TacticT jdg ext m ()
try t = t <|> pure ()

-- | Runs a tactic repeatedly until it fails
many_ :: (MonadProvable jdg m, MonadLogic m) => TacticT jdg ext m () -> TacticT jdg ext m ()
many_ t = try (t >> many_ t)

-- | Get the current goal
goal :: (Monad m) => TacticT jdg ext m jdg
goal = TacticT $ get


-- | @choice err ts@ tries to apply a series of tactics @ts@, and commits to the
-- 1st tactic that succeeds. If they all fail, then @err@ is thrown
choice :: (MonadProvable jdg m, MonadLogic m, MonadError err m) => err -> [TacticT jdg ext m a] -> TacticT jdg ext m a
choice err [] = throwError err
choice err (t:ts) = t <|> choice err ts

-- | @progress eq err t@ applies the tactic @t@, and checks to see if the
-- resulting subgoals are all equal to the initial goal by using @eq@. If they
-- are, it throws @err@.
progress :: (MonadProvable jdg m, MonadError err m) => (jdg -> jdg -> Bool) -> err ->  TacticT jdg ext m a -> TacticT jdg ext m a
progress eq err t = do
  j <- goal
  a <- t
  j' <- goal
  if j `eq` j' then pure a else throwError err

-- | Apply the first tactic, and then apply the second tactic focused on the @n@th subgoal.
focus :: (MonadProvable jdg m, Monad m) => TacticT jdg ext m () -> Int -> TacticT jdg ext m () -> TacticT jdg ext m ()
focus t ix t' = stateful t applyTac 0
  where
    applyTac j = do
      n <- get
      put (n + 1)
      hoist lift $ asRule j (if n == ix then t' else pure ())

-- | Applies @f@ to every subgoals resulting from the tactic @t@.
forSubgoals :: (Monad m) => TacticT jdg ext m a -> (jdg -> m b) -> TacticT jdg ext m a
forSubgoals t f = TacticT $ StateT $ \j -> ProofStateT $
   action >\\ (unProofStateT $ runStateT (unTacticT t) j)
  where
    action (a, j) = do
      lift $ f j
      request (a, j)

-- | Runs a tactic, producing the extract, along with a list of unsolved subgoals.
runTacticT :: (MonadExtract jdg ext m) => TacticT jdg ext m () -> jdg -> m (ext, [jdg])
runTacticT (TacticT t) j =
  fmap (second reverse) $ flip runStateT [] $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t j)
  where
    server :: (MonadExtract jdg ext m) => jdg -> Server jdg ext (StateT [jdg] m) ext
    server j = do
      modify (j:)
      h <- hole j
      respond h >>= server

class (Monad m) => MonadExtract jdg ext m | m -> ext where
  -- | Generates a "hole" of type @ext@, which should represent
  -- an incomplete extract.
  hole :: jdg -> m ext
  default hole :: (MonadTrans t, MonadExtract jdg ext m1, m ~ t m1) => jdg -> m ext
  hole = lift . hole

instance (MonadExtract jdg ext m) => MonadExtract jdg ext (Proxy a' a b' b m)
instance (MonadExtract jdg ext m) => MonadExtract jdg ext (StateT s m)
instance (MonadExtract jdg ext m) => MonadExtract jdg ext (ReaderT env m)
instance (MonadExtract jdg ext m) => MonadExtract jdg ext (ExceptT err m)
instance (MonadExtract jdg ext m) => MonadExtract jdg ext (RuleT jdg ext m)


-- | Turn an inference rule into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext m ext) -> TacticT jdg ext m ()
rule r = TacticT $ StateT $ \j -> ProofStateT $ (\j' -> request ((), j')) >\\ unRuleT (r j)

-- | Turn an inference rule using ReaderT into a tactic.
readerRule :: (Monad m) => ReaderT jdg (RuleT jdg ext m) ext -> TacticT jdg ext m ()
readerRule r = TacticT $ StateT $ \j -> ProofStateT $ (\j' -> request ((), j')) >\\ (unRuleT $ runReaderT r j)