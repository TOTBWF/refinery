-- |
-- Module      :  Refinery.SearchT
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Refinery.SearchT
  ( SearchT
  , observeT
  , observeManyT
  ) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Logic.Class
import Control.Monad.Identity

import Data.List.NonEmpty

newtype SearchT err m a = SearchT { unSearchT :: forall r. (a -> m r -> m r) -> (a -> m r) -> (err -> m r) -> m r}
type Search err a = SearchT err Identity a

instance Functor (SearchT err m) where
  fmap f st = SearchT $ \mk sk fk -> unSearchT st (mk . f) (sk . f) fk

instance Applicative (SearchT err m) where
  pure a = SearchT $ \mk sk fk -> sk a
  f <*> a = SearchT $ \mk sk fk -> unSearchT f (\g sk' -> unSearchT a (mk . g) (sk . g) (const sk')) (\g -> unSearchT a (mk . g) (sk . g) fk) fk

instance (Monoid err) => Alternative (SearchT err m) where
  empty = SearchT $ \_ _ fk -> fk mempty
  f1 <|> f2 = SearchT $ \mk sk fk -> unSearchT f1 mk sk (\err -> unSearchT f2 mk sk (\err' -> fk (err <> err')))

instance Monad (SearchT err m) where
  return = pure
  m >>= f = SearchT $ \mk sk fk -> unSearchT m (\a sk' -> unSearchT (f a) mk sk (const sk')) (\a -> unSearchT (f a) mk sk fk) fk

instance MonadTrans (SearchT err) where
  lift m = SearchT $ \mk sk fk -> m >>= \a -> sk a

instance (Monoid err) => MonadPlus (SearchT err m) where
  mzero = empty
  mplus = (<|>)

instance (Monoid err, Monad m) => MonadLogic (SearchT err m) where
  msplit m = lift $ unSearchT m (\a sk -> return $ Just (a, lift sk >>= reflect)) (\a -> return $ Just (a, throwError mempty)) (const $ return Nothing)
  once m = SearchT $ \mk sk fk -> unSearchT m (\a _ -> sk a) sk fk

instance MonadError err (SearchT err m) where
  throwError err = SearchT $ \mk sk fk -> fk err
  catchError m h = SearchT $ \mk sk fk -> unSearchT m mk sk (\err -> unSearchT (h err) mk sk fk)

observeT :: (Monad m) => SearchT err m a -> m (Either err a)
observeT st = unSearchT st (const . return . Right) (return . Right) (return . Left)

observeManyT :: (Monad m) => SearchT err m a -> m (Either err (NonEmpty a))
observeManyT st = unSearchT st (\a as -> fmap (fmap (cons a)) as) (return . Right . singleton) (return . Left)
  where
    singleton :: a -> NonEmpty a
    singleton a = a :| []

observeMany :: Search err a -> Either err (NonEmpty a)
observeMany = runIdentity . observeManyT