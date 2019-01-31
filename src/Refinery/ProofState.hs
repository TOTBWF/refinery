{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Refinery.ProofState
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
module Refinery.ProofState
  ( ProofStateT(..)
  , axiom
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.IO.Class

import Pipes.Core

newtype ProofStateT ext m jdg = ProofStateT { unProofStateT :: Client jdg ext m ext }

instance (Monad m) => Functor (ProofStateT ext m) where
  fmap f (ProofStateT p) = ProofStateT $ (request . f) >\\ p

instance (Monad m) => Applicative (ProofStateT ext m) where
  pure a = ProofStateT $ request a
  (ProofStateT pf) <*> (ProofStateT pa) = ProofStateT $ (\f -> (request . f) >\\ pa) >\\ pf

instance (Monad m) => Monad (ProofStateT ext m) where
  return = pure
  (ProofStateT p) >>= k = ProofStateT $ (unProofStateT . k) >\\ p

instance MonadTrans (ProofStateT ext) where
  lift m = ProofStateT $ request =<< (lift m)

instance (MonadIO m) => MonadIO (ProofStateT ext m) where
  liftIO m = ProofStateT $ request =<< (liftIO m)

instance (MonadError err m) => MonadError err (ProofStateT ext m) where
  throwError e = ProofStateT $ lift $ throwError e
  catchError (ProofStateT m) h = ProofStateT $ catchError m (unProofStateT . h)

instance (MonadReader env m) => MonadReader env (ProofStateT ext m) where
  ask = lift ask
  local f (ProofStateT m) = ProofStateT $ local f m

instance (MonadState s m) => MonadState s (ProofStateT ext m) where
  get = lift get
  put = lift . put

axiom :: (Monad m) => ext -> ProofStateT ext m jdg
axiom e = ProofStateT $ return e
