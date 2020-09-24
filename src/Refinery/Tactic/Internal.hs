{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}

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
  -- , stateful
  -- , asRule
  , MonadRule(..)
  , RuleT(..)
  , mapRuleT
  , MonadProvable(..)
  , ProvableT(..)
  , Provable
  , runProvable
  )
where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Catch
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans
import Control.Monad.Logic
import Control.Monad.IO.Class
import Control.Monad.Morph

import Data.Bifunctor
import Data.Coerce

import Pipes.Core
import Pipes.Internal
import Pipes.Lift (evalStateP, runStateP)

import Refinery.ProofState

-- | A @'TacticT'@ is a monad transformer that performs proof refinement.
-- The type variables signifiy:
--
-- * @jdg@ - The goal type. This is the thing we are trying to construct a proof of.
-- * @ext@ - The extract type. This is what we will recieve after running the tactic.
-- * @m@ - The base monad.
-- * @a@ - The return value. This to make @'TacticT'@ a monad, and will always be @'()'@
newtype TacticT jdg ext err m a = TacticT { unTacticT :: StateT jdg (ProofStateT ext ext err m) a }
  deriving ( Functor
           , Alternative
           , MonadPlus
           , MonadReader env
           , MonadError err
           , MonadIO
           , MonadThrow
           , MonadCatch
           )

instance (MonadProvable jdg m) => Applicative (TacticT jdg ext err m) where
  pure a = TacticT $ StateT $ proving >=> \j -> pure (a, j)
  (<*>) = ap

instance (MonadProvable jdg m) => Monad (TacticT jdg ext err m) where
  return = pure
  t >>= k = TacticT $ StateT $ proving >=> \j -> do
    (a, j') <- runStateT (unTacticT t) j
    runStateT (unTacticT $ k a) =<< proving j'

-- | Map the unwrapped computation using the given function
mapTacticT :: (Monad m) => (m a -> m b) -> TacticT jdg ext err m a -> TacticT jdg ext err m b
mapTacticT f (TacticT m) = TacticT $ m >>= (lift . lift . f . return)

instance MonadTrans (TacticT jdg ext err) where
  lift m = TacticT $ lift $ lift m

instance (MonadProvable jdg m, MonadState s m) => MonadState s (TacticT jdg ext err m) where
  get = lift get
  put = lift . put

-- -- | Helper function for making "stateful" tactics like "<@>"
-- stateful :: (Monad m) => TacticT jdg ext err m a -> (jdg -> RuleT jdg ext (StateT s m) ext) -> s -> TacticT jdg ext err m a
-- stateful (TacticT t) f s = TacticT $ StateT $ \j -> ProofStateT $
--   evalStateP s $ action >\\ (hoist lift $ unProofStateT $ runStateT t j)
--   where
--     action (a, j) = (\j' -> request (a, j')) >\\ (unRuleT $ f j)

-- -- | Transforms a tactic into a rule. Useful for doing things with @'stateful'@.
-- asRule :: (Monad m) => jdg -> TacticT jdg ext err m a -> RuleT jdg ext m ext
-- asRule j t = RuleT $ unProofStateT $ execStateT (unTacticT t) j

-- | A @'RuleT'@ is a monad transformer for creating inference rules.
newtype RuleT jdg ext err m a = RuleT
  { unRuleT :: ProofStateT ext a err m jdg
  }

instance Functor m => Functor (RuleT jdg ext err m) where
  fmap = coerce mapExtract'

instance Monad m => Applicative (RuleT jdg ext err m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (RuleT jdg ext err m) where
  RuleT (Subgoal goal k) >>= f = coerce $ Subgoal goal $ fmap (bindAlaCoerce f) k
  RuleT (Effect m)       >>= f = coerce $ Effect $ fmap (bindAlaCoerce f) m
  RuleT (Alt p1 p2)      >>= f = coerce $ Alt (bindAlaCoerce f p1) (bindAlaCoerce f p2)
  RuleT Empty            >>= _ = coerce $ Empty
  RuleT (Failure err)    >>= _ = coerce $ Failure err
  RuleT (Axiom e)        >>= f = f e

bindAlaCoerce
  :: (Monad m, Coercible c (m b), Coercible a1 (m a2)) =>
     (a2 -> m b) -> a1 -> c
bindAlaCoerce f = coerce . (f =<<) . coerce

instance MonadTrans (RuleT jdg ext err) where
  lift = coerce . Effect . fmap Axiom

instance MFunctor (RuleT jdg ext err) where
  hoist nat = hoist nat . coerce


--   deriving ( Functor
--            , Applicative
--            , Monad
--            , MonadReader env
--            , MonadState s
--            , MonadError err
--            , MonadIO
--            , MonadThrow
--            , MonadCatch
--            , MonadTrans
--            , MFunctor
--            )

-- | Map the unwrapped computation using the given function
mapRuleT :: (Monad m) => (m a -> m b) -> RuleT jdg ext err m a -> RuleT jdg ext err m b
mapRuleT f (RuleT m) = undefined -- RuleT $ m >>= (lift . f . return)

class (Monad m) => MonadRule jdg ext m | m -> jdg, m -> ext where
  -- | Create a subgoal, and return the resulting extract.
  subgoal :: jdg -> m ext
  default subgoal :: (MonadTrans t, MonadRule jdg ext m1, m ~ t m1) => jdg -> m ext
  subgoal = lift . subgoal

instance (Monad m) => MonadRule jdg ext (RuleT jdg ext err m) where
  subgoal j = undefined -- RuleT $ request j

instance (MonadRule jdg ext m) => MonadRule jdg ext (ReaderT env m)
instance (MonadRule jdg ext m) => MonadRule jdg ext (StateT env m)
instance (MonadRule jdg ext m) => MonadRule jdg ext (ExceptT env m)
instance (MonadRule jdg ext m) => MonadRule jdg ext (ProvableT env m)

class (Monad m) => MonadProvable jdg m | m -> jdg where
  -- | Applies a transformation of goals at every step of the tactic.
  proving :: jdg -> m jdg
  default proving :: (MonadTrans t, MonadProvable jdg m1, m ~ t m1) => jdg -> m jdg
  proving = lift . proving

instance (MonadProvable jdg m) => MonadProvable jdg (ProofStateT ext ext err m)
instance (MonadProvable jdg m) => MonadProvable jdg (ReaderT r m)
instance (MonadProvable jdg m) => MonadProvable jdg (StateT s m)
instance (MonadProvable jdg m) => MonadProvable jdg (ExceptT err m)
instance (Monad m) => MonadProvable jdg (ProvableT jdg m) where
  proving = pure

-- | Helper newtype for when you don't have any need for the mechanisms of MonadProvable.
newtype ProvableT jdg m a = ProvableT { runProvableT :: m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState s, MonadError err)

type Provable jdg a = ProvableT jdg Identity a

instance MonadTrans (ProvableT jdg) where
  lift = ProvableT

runProvable :: Provable jdg a -> a
runProvable = runIdentity . runProvableT
