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
  , (<@>),
    MonadExtract(..)
  , RuleT
  , MonadRule(..)
  , rule
  -- * Re-Exports
  , Alt(..)
  ) where

import Data.Functor.Alt
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans
import Control.Monad.IO.Class
import Control.Monad.Morph

import Data.Bifunctor

import Pipes.Core
import Pipes.Lift (distribute)

import Refinery.ProofState
import Refinery.Tactic.Internal

-- | Create a tactic that applies each of the tactics in the list to one subgoal.
--
-- When the number of subgoals is greater than the number of provided tactics,
-- the identity tactic is applied to the remainder. When the number of subgoals is
-- less than the number of provided tactics, the remaining tactics are ignored.
(<@>) :: (Monad m) => TacticT jdg ext m () -> [TacticT jdg ext m ()] -> TacticT jdg ext m ()
t <@> ts = stateful t applyTac (ts ++ repeat (pure ()))
  where
    applyTac j = do
      t <- gets (unTacticT . head)
      modify tail
      RuleT $ hoist lift $ unProofStateT $ execStateT t j

-- | Runs a tactic, producing the extract, along with a list of unsolved subgoals.
runTacticT :: (MonadExtract ext m) => TacticT jdg ext m () -> jdg -> m (ext, [jdg])
runTacticT (TacticT t) j =
  fmap (second reverse) $ flip runStateT [] $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t j)
  where
    server :: (MonadExtract ext m) => jdg -> Server jdg ext (StateT [jdg] m) ext
    server j = do
      modify (j:)
      h <- hole
      respond h >>= server

class (Monad m) => MonadExtract ext m | m -> ext where
  -- | Generates a "hole" of type @ext@, which should represent
  -- an incomplete extract.
  hole :: m ext
  default hole :: (MonadTrans t, MonadExtract ext m1, m ~ t m1) => m ext
  hole = lift hole

instance (MonadExtract ext m) => MonadExtract ext (Proxy a' a b' b m)
instance (MonadExtract ext m) => MonadExtract ext (StateT s m)
instance (MonadExtract ext m) => MonadExtract ext (ReaderT env m)
instance (MonadExtract ext m) => MonadExtract ext (ExceptT err m)

class (Monad m) => MonadRule jdg ext m | m -> jdg, m -> ext where
  -- | Create a subgoal, and return the resulting extract.
  subgoal :: jdg -> m ext
  default subgoal :: (MonadTrans t, MonadRule jdg ext m1, m ~ t m1) => jdg -> m ext
  subgoal = lift . subgoal

instance (Monad m) => MonadRule jdg ext (RuleT jdg ext m) where
  subgoal j = RuleT $ request j

instance (MonadRule jdg ext m) => MonadRule jdg ext (ReaderT env m)
instance (MonadRule jdg ext m) => MonadRule jdg ext (StateT env m)
instance (MonadRule jdg ext m) => MonadRule jdg ext (ExceptT env m)

-- | Turn an inference rule into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext m ext) -> TacticT jdg ext m ()
rule r = TacticT $ StateT $ \j -> ProofStateT $ (\j' -> request ((), j')) >\\ unRuleT (r j)
