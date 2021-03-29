{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
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
  , tactic
  , proofState
  , proofState_
  , mapTacticT
  -- * Rules
  , RuleT(..)
  , subgoal
  , unsolvable
  )
where

import GHC.Generics
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Catch
import Control.Monad.State.Strict
import Control.Monad.Trans ()
import Control.Monad.IO.Class ()
import Control.Monad.Morph

import Data.Coerce

import Refinery.ProofState

-- | A @'TacticT'@ is a monad transformer that performs proof refinement.
-- The type variables signifiy:
--
-- * @jdg@ - The goal type. This is the thing we are trying to construct a proof of.
-- * @ext@ - The extract type. This is what we will recieve after running the tactic.
-- * @err@ - The error type. We can use 'throwError' to abort the computation with a provided error
-- * @s@   - The state type.
-- * @m@   - The base monad.
-- * @a@   - The return value. This to make @'TacticT'@ a monad, and will always be @'Prelude.()'@
--
-- One of the most important things about this type is it's 'Monad' instance. @t1 >> t2@
-- Will execute @t1@ against the current goal, and then execute @t2@ on _all_ of the subgoals generated
-- by @t2@.
--
-- This Monad instance is lawful, and has been tested thouroughly, and a version of it has been formally verified in Agda.
-- _However_, just because it is correct doesn't mean that it lines up with your intuitions of how Monads behave!
-- In practice, it feels like a combination of the Non-Determinisitic Monads and some of the Time Travelling ones.
-- That doesn't mean that it's impossible to understand, just that it may push the boundaries of you intuitions.
newtype TacticT jdg ext err s m a = TacticT { unTacticT :: StateT jdg (ProofStateT ext ext err s m) a }
  deriving ( Functor
           , Applicative
           , Alternative
           , Monad
           , MonadPlus
           , MonadIO
           , MonadThrow
           , Generic
           )

instance (Monoid jdg, Show a, Show jdg, Show err, Show ext, Show (m (ProofStateT ext ext err s m (a, jdg)))) => Show (TacticT jdg ext err s m a) where
  show = show . flip runStateT mempty . unTacticT

-- | Helper function for producing a tactic.
tactic :: (jdg -> ProofStateT ext ext err s m (a, jdg)) -> TacticT jdg ext err s m a
tactic t = TacticT $ StateT t

-- | @proofState t j@ will deconstruct a tactic @t@ into a 'ProofStateT' by running it at @j@.
proofState :: TacticT jdg ext err s m a -> jdg -> ProofStateT ext ext err s m (a, jdg)
proofState t j = runStateT (unTacticT t) j

-- | Like 'proofState', but we discard the return value of @t@.
proofState_ :: (Functor m) => TacticT jdg ext err s m a -> jdg -> ProofStateT ext ext err s m jdg
proofState_ t j = execStateT (unTacticT t) j

-- | Map the unwrapped computation using the given function
mapTacticT :: (Monad m) => (m a -> m b) -> TacticT jdg ext err s m a -> TacticT jdg ext err s m b
mapTacticT f (TacticT m) = TacticT $ m >>= (lift . lift . f . return)

instance MFunctor (TacticT jdg ext err s) where
  hoist f = TacticT . (hoist (hoist f)) . unTacticT

instance MonadTrans (TacticT jdg ext err s) where
  lift m = TacticT $ lift $ lift m


instance (Monad m) => MonadState s (TacticT jdg ext err s m) where
    state f = tactic $ \j -> fmap (,j) $ state f

-- | A @'RuleT'@ is a monad transformer for creating inference rules.
newtype RuleT jdg ext err s m a = RuleT
  { unRuleT :: ProofStateT ext a err s m jdg
  }
  deriving stock Generic

instance (Show jdg, Show err, Show a, Show (m (ProofStateT ext a err s m jdg))) => Show (RuleT jdg ext err s m a) where
  show = show . unRuleT

instance Functor m => Functor (RuleT jdg ext err s m) where
  fmap f = coerce (mapExtract id f)

instance Monad m => Applicative (RuleT jdg ext err s m) where
  pure = return
  (<*>) = ap

instance Monad m => Alternative (RuleT jdg ext err s m) where
    empty = coerce Empty
    (<|>) = coerce Alt

instance Monad m => Monad (RuleT jdg ext err s m) where
  return = coerce . Axiom
  RuleT (Subgoal goal k)   >>= f = coerce $ Subgoal goal $ fmap (bindAlaCoerce f) k
  RuleT (Effect m)         >>= f = coerce $ Effect $ fmap (bindAlaCoerce f) m
  RuleT (Stateful s)       >>= f = coerce $ Stateful $ fmap (bindAlaCoerce f) . s
  RuleT (Alt p1 p2)        >>= f = coerce $ Alt (bindAlaCoerce f p1) (bindAlaCoerce f p2)
  RuleT (Interleave p1 p2) >>= f = coerce $ Interleave (bindAlaCoerce f p1) (bindAlaCoerce f p2)
  RuleT (Commit p1 p2)     >>= f = coerce $ Commit (bindAlaCoerce f p1) (bindAlaCoerce f p2)
  RuleT Empty              >>= _ = coerce $ Empty
  RuleT (Failure err k)    >>= f = coerce $ Failure err $ fmap (bindAlaCoerce f) k
  RuleT (Handle p h)       >>= f = coerce $ Handle (bindAlaCoerce f p) h
  RuleT (Axiom e)          >>= f = f e

instance Monad m => MonadState s (RuleT jdg ext err s m) where
    state f = RuleT $ Stateful $ \s ->
        let (a, s') = f s
        in (s', Axiom a)

bindAlaCoerce
  :: (Monad m, Coercible c (m b), Coercible a1 (m a2)) =>
     (a2 -> m b) -> a1 -> c
bindAlaCoerce f = coerce . (f =<<) . coerce

instance MonadTrans (RuleT jdg ext err s) where
  lift = coerce . Effect . fmap Axiom

instance MFunctor (RuleT jdg ext err s) where
  hoist nat = hoist nat . coerce

instance MonadIO m => MonadIO (RuleT jdg ext err s m) where
  liftIO = lift . liftIO

-- | Create a subgoal, and return the resulting extract.
subgoal :: jdg -> RuleT jdg ext err s m ext
subgoal jdg = RuleT $ Subgoal jdg Axiom

-- | Create an "unsolvable" hole. These holes are ignored by subsequent tactics,
-- but do not cause a backtracking failure.
unsolvable :: err -> RuleT jdg ext err s m ext
unsolvable err = RuleT $ Failure err Axiom
