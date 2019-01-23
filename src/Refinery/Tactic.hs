-----------------------------------------------------------------------------
-- |
-- Module      :  Refinery.Tactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = Tactics
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Refinery.Tactic
  ( TacticT
  , runTacticT
  , (<@>)
  , Extract(..)
  , RuleT
  , MonadRule(..)
  , rule
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

-- | A monad transformer for tactics.
newtype TacticT jdg ext m a = TacticT { unTacticT :: StateT jdg (ProofStateT ext m) a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance (MonadError err m) => Alt (TacticT jdg ext m) where
  (TacticT t1) <!> (TacticT t2) = TacticT $ t1 `catchError` (const t2)

instance MonadTrans (TacticT jdg ext) where
  lift m = TacticT $ lift $ lift m

-- | Helper function for making "stateful" tactics like "<@>"
stateful :: (Monad m) => TacticT jdg ext m () -> (jdg -> RuleT jdg ext (StateT s m) ext) -> s -> TacticT jdg ext m ()
stateful (TacticT t) f s = TacticT $ StateT $ \j -> ProofStateT $
  flip evalStateT s $ distribute $ action >\\ (hoist lift $ unProofStateT $ runStateT t j)
  where
    action (_, j) = (\j' -> request ((), j')) >\\ (unRuleT $ f j)

(<@>) :: (Monad m) => TacticT jdg ext m () -> [TacticT jdg ext m ()] -> TacticT jdg ext m ()
t <@> ts = stateful t applyTac (ts ++ repeat (pure ()))
  where
    applyTac j = do
      t <- gets (unTacticT . head)
      modify tail
      RuleT $ hoist lift $ unProofStateT $ execStateT t j

-- | Runs a tactic, producing the extract, along with a list of unsolved subgoals.
runTacticT :: (Monad m, Extract ext) => TacticT jdg ext m () -> jdg -> m (ext, [jdg])
runTacticT (TacticT t) j =
  fmap (second reverse) $ flip runStateT [] $ runEffect $ server +>> (hoist lift $ unProofStateT $ execStateT t j)
  where
    server :: (Monad m, Extract ext) => jdg -> Server jdg ext (StateT [jdg] m) ext
    server j = do
      modify (j:)
      respond hole >>= server

-- TODO: Figure out the proper way to have this work, there may need to be a monad in here somewhere.
class Extract ext where
  -- | An @Extract@ must have some concept of a hole, so that tactics that
  -- have unsolved subgoals can still run to completion.
  hole :: ext

-- | A monad transformer for creating inference-rule tactics.
newtype RuleT jdg ext m a = RuleT { unRuleT :: Client jdg ext m a }
  deriving (Functor, Applicative, Monad, MonadState s, MonadError err, MonadIO, MonadTrans)

class (Monad m) => MonadRule jdg ext m | m -> jdg, m -> ext where
  subgoal :: jdg -> m ext

instance (Monad m) => MonadRule jdg ext (RuleT jdg ext m) where
  subgoal j = RuleT $ request j

instance (MonadRule jdg ext m) => MonadRule jdg ext (ReaderT env m) where
  subgoal j = lift $ subgoal j

-- | Turn an inference rule into a tactic.
rule :: (Monad m) => (jdg -> RuleT jdg ext m ext) -> TacticT jdg ext m ()
rule r = TacticT $ StateT $ \j -> ProofStateT $ (\j' -> request ((), j')) >\\ unRuleT (r j)
