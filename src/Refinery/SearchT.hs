-- |
-- Module      :  Refinery.SearchT
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module Refinery.SearchT
  ( SearchT
  , observeT
  , observeAllT
  , asumWith
  ) where

import Data.Functor.Alt
import Data.Semigroup hiding (Alt)
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Logic.Class
import Control.Monad.Identity

import Data.List.NonEmpty
import Data.Either

newtype SearchT err m a = SearchT { unSearchT :: forall r. (m r -> m r -> m r) -> (a -> m r) -> (err -> m r) -> m r}

type Search err a = SearchT err Identity a

instance Functor (SearchT err m) where
  fmap f st = SearchT $ \mk sk fk -> unSearchT st mk (sk . f) fk

instance Applicative (SearchT err m) where
  pure a = SearchT $ \_ sk _ -> sk a
  f <*> a = SearchT $ \mk sk fk -> unSearchT f mk (\g -> unSearchT a mk (sk . g) fk) fk


instance Alt (SearchT err m) where
  f1 <!> f2 = SearchT $ \mk sk fk ->
    unSearchT f1 mk (\a -> mk (sk a) (unSearchT f2 mk sk fk)) fk

instance (Monoid err) => Alternative (SearchT err m) where
  empty = SearchT $ \mk sk fk -> fk mempty
  (<|>) = (<!>)

instance Monad (SearchT err m) where
  return = pure
  m >>= f = SearchT $ \mk sk fk -> unSearchT m mk (\a -> unSearchT (f a) mk sk fk) fk

instance MonadTrans (SearchT err) where
  lift m = SearchT $ \mk sk fk -> m >>= sk

instance (MonadIO m) => MonadIO (SearchT err m) where
  liftIO m = SearchT $ \mk sk fk -> liftIO m >>= sk

instance (Monoid err) => MonadPlus (SearchT err m) where
  mzero = empty
  mplus = (<|>)

instance (Monoid err, Monad m) => MonadLogic (SearchT err m) where
  msplit m = lift $ unSearchT m (liftA2 combine) (\a -> return $ Just (a, empty)) (const $ return Nothing)
      where
        combine :: (Monoid err) => Maybe (a, SearchT err m a) -> Maybe (a, SearchT err m a) -> Maybe (a, SearchT err m a)
        combine Nothing r = r
        combine l Nothing = l
        combine (Just (a, f1)) (Just (a', f2)) = Just (a, f1 <|> pure a' <|> f2)

instance MonadError err (SearchT err m) where
  throwError err = SearchT $ \mk sk fk -> fk err
  catchError m h = SearchT $ \mk sk fk -> unSearchT m mk sk (\err -> unSearchT (h err) mk sk fk)

observeT :: (Monad m) => SearchT err m a -> m (Either err a)
observeT st = unSearchT st const (return . Right) (return . Left)

observeAllT :: (Monoid err, Monad m) => SearchT err m a -> m (Either err (NonEmpty a))
observeAllT st = unSearchT st (liftA2 combine) (return . Right . singleton) (return . Left)
  where
    combine :: (Semigroup m, Semigroup err) => Either err m -> Either err m -> Either err m
    combine (Left e) (Left e') = Left (e <> e')
    combine (Right m) (Right m') = Right (m <> m')
    combine (Right m) _ = Right m
    combine _ (Right m) = Right m

    singleton :: a -> NonEmpty a
    singleton a = a :| []

observe :: Search err a -> Either err a
observe = runIdentity . observeT

observeAll :: (Monoid err) => Search err a -> Either err (NonEmpty a)
observeAll = runIdentity . observeAllT

asumWith :: (Foldable t, Alternative f) => f a -> t (f a) -> f a
asumWith = foldr (<|>)


newtype ContE err m a = ContE { runContE :: forall r. (err -> m r) -> (a -> m r) -> m r }

-- ContE err (State s) a
-- forall r. (err -> State s r) -> (a -> State s r) -> State s r