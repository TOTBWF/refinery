{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Refinery.Proof 
    (
      ProofState(..)
    , mapAccumLM
    , mapAccumRM
    -- , (|>)
    -- , singleton
    -- , concat
    ) where

import Prelude hiding (concat)

import Data.Functor.Identity
import Control.Applicative
import Control.Monad
 

import Refinery.Telescope (Telescope(..), (@>))
import qualified Refinery.Telescope as Tl
import Refinery.MetaSubst

data ProofState ext jdg
  = Subgoals (Telescope ext (ProofState ext jdg)) ext
  | Unsolved jdg
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (MetaVar ext), Show ext, Show jdg) => Show (ProofState ext jdg)

instance Applicative (ProofState ext) where
  pure = return
  (<*>) = ap

instance Monad (ProofState ext) where
  return = Unsolved
  (Unsolved j) >>= f = f j
  (Subgoals goals ext) >>= f = Subgoals (fmap (\p -> p >>= f) goals) ext

-- Traversable extensions
newtype StateLT s m a = StateLT { runStateLT :: s -> m (s,a) }

instance (Functor m) => Functor (StateLT s m) where
  fmap f (StateLT k) = StateLT $ \s -> fmap (\(s',a) -> (s', f a)) $ k s

instance Monad m => Applicative (StateLT s m) where
  pure a = StateLT $ \s -> return (s, a)
  StateLT kf <*> StateLT kv = StateLT $ \s -> do
    (s', f) <- kf s
    (s'', v) <- kv s'
    return (s'', f v)
  liftA2 f (StateLT kx) (StateLT ky) = StateLT $ \s -> do
    (s', x) <- kx s
    (s'', y) <- ky s'
    return (s'', f x y)

mapAccumLM :: (Monad m, Traversable t) => (a -> b -> m (a,c)) -> a -> t b -> m (a, t c)
mapAccumLM f s t = runStateLT (traverse (StateLT . flip f) t) s

newtype StateRT s m a = StateRT { runStateRT :: s -> m (s,a) }

instance (Functor m) => Functor (StateRT s m) where
  fmap f (StateRT k) = StateRT $ \s -> fmap (\(s',a) -> (s', f a)) $ k s

instance Monad m => Applicative (StateRT s m) where
  pure a = StateRT $ \s -> return (s, a)
  StateRT kf <*> StateRT kv = StateRT $ \s -> do
    (s', v) <- kv s
    (s'', f) <- kf s'
    return (s'', f v)
  liftA2 f (StateRT kx) (StateRT ky) = StateRT $ \s -> do
    (s', y) <- ky s
    (s'', x) <- kx s'
    return (s'', f x y)

mapAccumRM :: (Monad m, Traversable t) => (a -> b -> m (a,c)) -> a -> t b -> m (a, t c)
mapAccumRM f s t = runStateRT (traverse (StateRT . flip f) t) s
