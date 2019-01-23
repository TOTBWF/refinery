{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Refinery.ProofState where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
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

axiom :: (Monad m) => ext -> ProofStateT ext m jdg
axiom e = ProofStateT $ return e