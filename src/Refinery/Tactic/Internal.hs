{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Refinery.Tactic.Internal
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
-- = WARNING
-- This module is considered __internal__, and can
-- change at any given time.
module Refinery.Tactic.Internal
  ( TacticT(..)
  , mapTacticT
  , stateful
  , RuleT(..)
  , mapRuleT
  )
where

import Data.Functor.Alt
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Catch
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans
import Control.Monad.IO.Class
import Control.Monad.Morph

import Data.Bifunctor

import Pipes.Core
import Pipes.Lift (distribute)

import Refinery.ProofState

-- | A @'TacticT'@ is a monad transformer that performs proof refinement.
-- The type variables signifiy:
--
-- * @jdg@ - The goal type. This is the thing we are trying to construct a proof of.
-- * @ext@ - The extract type. This is what we will recieve after running the tactic.
-- * @m@ - The base monad.
-- * @a@ - The return value. This to make @'TacticT'@ a monad, and will always be @'()'@
newtype TacticT jdg ext m a = TacticT { unTacticT :: StateT jdg (ProofStateT ext m) a }
  deriving (Functor, Applicative, Monad, MonadReader env, MonadError err, MonadIO, MonadThrow, MonadCatch)

-- | Map the unwrapped computation using the given function
mapTacticT :: (Monad m) => (m a -> m b) -> TacticT jdg ext m a -> TacticT jdg ext m b
mapTacticT f (TacticT m) = TacticT $ m >>= (lift . lift . f . return)

instance (MonadError err m) => Alt (TacticT jdg ext m) where
  (TacticT t1) <!> (TacticT t2) = TacticT $ t1 `catchError` (const t2)

instance MonadTrans (TacticT jdg ext) where
  lift m = TacticT $ lift $ lift m

instance (MonadState s m) => MonadState s (TacticT jdg ext m) where
  get = lift get
  put = lift . put

-- | Helper function for making "stateful" tactics like "<@>"
stateful :: (Monad m) => TacticT jdg ext m () -> (jdg -> RuleT jdg ext (StateT s m) ext) -> s -> TacticT jdg ext m ()
stateful (TacticT t) f s = TacticT $ StateT $ \j -> ProofStateT $
  flip evalStateT s $ distribute $ action >\\ (hoist lift $ unProofStateT $ runStateT t j)
  where
    action (_, j) = (\j' -> request ((), j')) >\\ (unRuleT $ f j)

-- | A @'RuleT'@ is a monad transformer for creating inference rules.
newtype RuleT jdg ext m a = RuleT { unRuleT :: Client jdg ext m a }
  deriving (Functor, Applicative, Monad, MonadReader env, MonadState s, MonadError err, MonadIO, MonadTrans)

-- | Map the unwrapped computation using the given function
mapRuleT :: (Monad m) => (m a -> m b) -> RuleT jdg ext m a -> RuleT jdg ext m b
mapRuleT f (RuleT m) = RuleT $ m >>= (lift . f . return)
