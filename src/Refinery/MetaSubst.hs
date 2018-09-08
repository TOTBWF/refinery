{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Refinery.MetaSubst 
  (
    SubstMeta(..)
  , MonadName(..)
  , MetaVar(..)
  , MetaSubst(..)
  ) where

import GHC.Generics

import Data.List (find)
import Data.Ratio
import Data.Word

data SubstMeta a b where
  SubstMeta :: (a ~ b) => MetaVar a -> SubstMeta a b

class (Monad m) => MonadName v m | v -> m where
  fresh :: m v

type family MetaVar a :: *

class (MonadName (MetaVar b) m, Eq (MetaVar b)) => MetaSubst b a m where

  isMetaVar :: a -> Maybe (SubstMeta a b)
  isMetaVar _ = Nothing

  metaSubst :: MetaVar b -> b -> a -> a
  metaSubsts :: [(MetaVar b, b)] -> a -> a

  default metaSubst :: (Generic a, GMetaSubst b (Rep a)) => MetaVar b -> b -> a -> a
  metaSubst n u x = case (isMetaVar x :: Maybe (SubstMeta a b)) of
    Just (SubstMeta m) | n == m -> u
    _ -> to $ gmetaSubst n u (from x)

  default metaSubsts :: (Generic a, GMetaSubst b (Rep a)) => [(MetaVar b, b)] -> a -> a
  metaSubsts ss x = case (isMetaVar x :: Maybe (SubstMeta a b)) of
    Just (SubstMeta m) | Just (_,u) <- find ((== m)  . fst) ss -> u
    _ -> to $ gmetaSubsts ss (from x)


class GMetaSubst a f where
  gmetaSubst :: MetaVar a -> a -> f c -> f c
  gmetaSubsts :: [(MetaVar a, a)] -> f c -> f c

instance (MetaSubst a b m) => GMetaSubst a (K1 i b) where
  gmetaSubst nm val = K1 . metaSubst nm val . unK1
  gmetaSubsts ss = K1 . metaSubsts ss . unK1

instance (GMetaSubst a f) => GMetaSubst a (M1 i c f) where
  gmetaSubst nm val = M1 . gmetaSubst nm val . unM1
  gmetaSubsts ss = M1 . gmetaSubsts ss . unM1

instance GMetaSubst a U1 where
  gmetaSubst _ _ _ = U1
  gmetaSubsts _ _ = U1

instance GMetaSubst a V1 where
  gmetaSubst _ _ = id
  gmetaSubsts _ = id

instance (GMetaSubst a f, GMetaSubst a g) => GMetaSubst a (f :*: g) where
  gmetaSubst nm val (f :*: g) = gmetaSubst nm val f :*: gmetaSubst nm val g
  gmetaSubsts ss (f :*: g) = gmetaSubsts ss f :*: gmetaSubsts ss g

instance (GMetaSubst a f, GMetaSubst a g) => GMetaSubst a (f :+: g) where
  gmetaSubst nm val (L1 f) = L1 $ gmetaSubst nm val f
  gmetaSubst nm val (R1 g) = R1 $ gmetaSubst nm val g

  gmetaSubsts ss (L1 f) = L1 $ gmetaSubsts ss f
  gmetaSubsts ss (R1 g) = R1 $ gmetaSubsts ss g

instance (Eq (MetaVar a), MonadName (MetaVar a) m) => MetaSubst a Char m where
  metaSubst _ _ = id
  metaSubsts _ = id

instance (Eq (MetaVar a), MonadName (MetaVar a) m) => MetaSubst a Integer m where
  metaSubst _ _ = id
  metaSubsts _ = id

instance (Eq (MetaVar a), MonadName (MetaVar a) m) => MetaSubst a (Ratio b) m where
  metaSubst _ _ = id
  metaSubsts _ = id

instance (Eq (MetaVar a), MonadName (MetaVar a) m) => MetaSubst a Word8 m where
  metaSubst _ _ = id
  metaSubsts _ = id

instance (Eq (MetaVar a), MonadName (MetaVar a) m) => MetaSubst a Int m  where
  metaSubst _ _ = id
  metaSubsts _ = id

instance (MetaSubst c a m, MetaSubst c b m) => MetaSubst c (a,b) m
instance (MetaSubst d a m, MetaSubst d b m, MetaSubst d c m) => MetaSubst d (a,b,c) m
instance (MetaSubst b a m) => MetaSubst b (Maybe a) m
instance (MetaSubst b a m) => MetaSubst b [a] m
