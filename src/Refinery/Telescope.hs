{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Refinery.Telescope
  (
    Telescope(..)
  , singleton
  , empty
  , (@>)
  , foldlWithVar, foldrWithVar
  , foldlMWithVar, foldrMWithVar
  , toList
  ) where

import Refinery.MetaSubst

data Telescope v t
  = Empty
  | Snoc (Telescope v t) (MetaVar v) t
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (MetaVar v), Show t) => Show (Telescope v t)

instance Semigroup (Telescope v t) where
  Empty <> t = t
  t <> Empty = t
  tl <> (Snoc tl' x a) = Snoc (tl <> tl') x a

instance Monoid (Telescope v t) where
  mempty = Empty

singleton :: MetaVar v -> t -> Telescope v t
singleton x t = Snoc Empty x t

empty :: Telescope v t
empty = Empty

(@>) :: Telescope v t -> (MetaVar v, t) -> Telescope v t
tl @> (v, t) = Snoc tl v t


foldlWithVar :: (b -> MetaVar v -> a -> b) -> b -> Telescope v a -> b
foldlWithVar _ b Empty = b
foldlWithVar f b (Snoc tl x a) = f (foldlWithVar f b tl) x a

foldrWithVar :: (MetaVar v -> a -> b -> b) -> b -> Telescope v a -> b
foldrWithVar _ b Empty = b
foldrWithVar f b (Snoc tl x a) = foldrWithVar f (f x a b) tl

foldlMWithVar :: (Monad m) => (b -> MetaVar v -> a -> m b) -> b -> Telescope v a -> m b
foldlMWithVar _ b Empty = return b
foldlMWithVar f b (Snoc tl x a) = do
  b' <- foldlMWithVar f b tl
  f b' x a

foldrMWithVar :: (Monad m) => (MetaVar v -> a -> b -> m b) -> b -> Telescope v a -> m b
foldrMWithVar _ b Empty = return b
foldrMWithVar f b (Snoc tl x a) = do
  b' <- f x a b
  foldrMWithVar f b' tl

toList :: Telescope v t -> [(MetaVar v,t)]
toList = foldrWithVar (\x t -> (:) (x,t)) []
