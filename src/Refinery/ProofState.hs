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
  , mapExtract
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.IO.Class

import Pipes.Core
import Pipes.Internal

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

instance (MonadPlus m) => Alternative (ProofStateT ext m) where
  empty = lift empty
  (ProofStateT p1) <|> (ProofStateT p2) = ProofStateT (go p1)
    where
      go (Request a' fa) = Request a' (go . fa)
      go (Respond b fb') = Respond b (go . fb')
      go (Pure r) = Pure r
      go (M m) = M ((go <$> m) <|> pure p2)

instance (MonadPlus m) => MonadPlus (ProofStateT ext m) where
  mzero = empty
  mplus = (<|>)

instance (MonadThrow m) => MonadThrow (ProofStateT ext m) where
  throwM e = ProofStateT $ lift $ throwM e

instance (MonadCatch m) => MonadCatch (ProofStateT ext m) where
  catch (ProofStateT m) h = ProofStateT $ catch m (unProofStateT . h)

instance (MonadReader env m) => MonadReader env (ProofStateT ext m) where
  ask = lift ask
  local f (ProofStateT m) = ProofStateT $ local f m

instance (MonadState s m) => MonadState s (ProofStateT ext m) where
  get = lift get
  put = lift . put

axiom :: (Monad m) => ext -> ProofStateT ext m jdg
axiom e = ProofStateT $ return e

mapExtract :: (Monad m) => (ext -> ext') -> (ext' -> ext) -> ProofStateT ext m jdg -> ProofStateT ext' m jdg
mapExtract into out p = ProofStateT $ fmap into ((\j ->  fmap out $ request j) >\\ (unProofStateT p))
