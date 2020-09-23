{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
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
  -- ( ProofStateT(..)
  -- , axiom
  -- , mapExtract
  -- )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Logic
import Control.Monad.Trans
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.IO.Class

-- import Pipes.Core
-- import Pipes.Internal

data ProofStateT ext err m goal
    = Subgoal goal (ext -> ProofStateT ext err m goal)
    | Effect (m (ProofStateT ext err m goal))
    | Alt (ProofStateT ext err m goal) (ProofStateT ext err m goal)
    | Empty
    | Failure err
    | Axiom ext

instance Functor m => Functor (ProofStateT ext err m) where
    fmap f (Subgoal goal k) = Subgoal (f goal) (fmap f . k)
    fmap f (Effect m) = Effect (fmap (fmap f) m)
    fmap f (Alt p1 p2) = Alt (fmap f p1) (fmap f p2)
    fmap f Empty = Empty
    fmap f (Failure err) = Failure err
    fmap f (Axiom ext) = Axiom ext

-- TODO Do this right pls
instance Monad m => Applicative (ProofStateT ext err m) where
    pure = return
    (<*>) = ap

applyCont :: (Functor m) => (ext -> ProofStateT ext err m a) -> ProofStateT ext err m a -> ProofStateT ext err m a
applyCont k (Subgoal goal k') = Subgoal goal (applyCont k . k')
applyCont k (Effect m) = Effect (fmap (applyCont k) m)
applyCont k (Alt p1 p2) = Alt (applyCont k p1) (applyCont k p2)
applyCont k Empty = Empty
applyCont k (Failure err) = (Failure err)
applyCont k (Axiom ext) = k ext

instance Monad m => Monad (ProofStateT ext err m) where
    return goal = Subgoal goal Axiom
    (Subgoal a k) >>= f = applyCont ((>>= f) . k) (f a)
    (Effect m)    >>= f = Effect (fmap (>>= f) m)
    (Alt p1 p2)   >>= f = Alt (p1 >>= f) (p2 >>= f)
    (Failure err) >>= _ = Failure err
    Empty         >>= _ = Empty
    (Axiom ext)   >>= _ = Axiom ext

instance MonadTrans (ProofStateT ext err) where
    lift m = Effect (fmap pure m)

instance (Monad m, Monoid err) => Alternative (ProofStateT ext err m) where
    empty = Empty
    (<|>) = Alt

instance (Monad m, Monoid err) => MonadPlus (ProofStateT ext err m) where
    mzero = empty
    mplus = (<|>)

instance (Monad m, Monoid err) => MonadLogic (ProofStateT ext err m) where
    msplit (Subgoal goal k) = Subgoal (Just (goal, Empty)) (msplit . k)
    msplit (Effect m)       = Effect (fmap msplit m)
    msplit (Alt p1 p2)      = msplit p1 >>= \case
        Just (a, rest) -> pure $ Just (a, rest <|> p2)
        Nothing        -> msplit p2
    msplit Empty            = pure Nothing
    msplit (Failure err)    = pure Nothing
    msplit (Axiom ext)      = pure Nothing

class (Monad m) => MonadExtract ext m | m -> ext where
  -- | Generates a "hole" of type @ext@, which should represent
  -- an incomplete extract.
  hole :: m ext
  default hole :: (MonadTrans t, MonadExtract ext m1, m ~ t m1) => m ext
  hole = lift hole

collect :: (MonadExtract ext m) => ProofStateT ext err m goal -> m (Either err [(ext, [goal])])
collect (Subgoal goal k) = do
    h <- hole
    pure $ Right $ [(h, [goal])]
collect (Effect m)       = collect =<< m
collect (Alt p1 p2)      = do
    e1 <- collect p1
    e2 <- collect p1
    -- FIXME: Sketchy but who cares
    pure (e1 <> e2)
collect Empty            = pure $ Right []
collect (Failure err)    = pure $ Left err
collect (Axiom ext)      = pure $ Right [(ext, [])]
-- instance MonadTrans (ProofStateT ext err) where
--     lift m = Effect $ fmap pure m
    -- (Pure a)      >>= f = _
      -- where
      --   go :: ProofStateT ext err m (a -> b) -> ProofStateT ext err m b
      --   go (Subgoal goal k) = _k
      --   -- go (M m) = M (fmap go _)
      --       -- M (fmap go m)
      --   go (Failure err) = Failure err
      --   go (Pure f) = fmap f px

    -- instance (Monad m) => Monad (ProofStateT ext err m) where
    -- return = pure

-- newtype ProofStateT ext m jdg = ProofStateT { unProofStateT :: Client jdg ext m ext }

-- instance (Monad m) => Functor (ProofStateT ext m) where
--   fmap f (ProofStateT p) = ProofStateT $ (request . f) >\\ p

-- instance (Monad m) => Applicative (ProofStateT ext m) where
--   pure a = ProofStateT $ request a
--   (ProofStateT pf) <*> (ProofStateT pa) = ProofStateT $ (\f -> (request . f) >\\ pa) >\\ pf

-- instance (Monad m) => Monad (ProofStateT ext m) where
--   return = pure
--   (ProofStateT p) >>= k = ProofStateT $ (unProofStateT . k) >\\ p

-- instance MonadTrans (ProofStateT ext) where
--   lift m = ProofStateT $ request =<< (lift m)

-- instance (MonadIO m) => MonadIO (ProofStateT ext m) where
--   liftIO m = ProofStateT $ request =<< (liftIO m)

-- instance (MonadError err m) => MonadError err (ProofStateT ext m) where
--   throwError e = ProofStateT $ lift $ throwError e
--   catchError (ProofStateT m) h = ProofStateT $ catchError m (unProofStateT . h)

-- instance (MonadPlus m) => Alternative (ProofStateT ext m) where
--   empty = lift empty
--   (ProofStateT p1) <|> (ProofStateT p2) = ProofStateT (go p1)
--     where
--       go (Request a' fa) = Request a' (go . fa)
--       go (Respond b fb') = Respond b (go . fb')
--       go (Pure r) = M (pure (Pure r) <|> pure p2)
--       go (M m) = M (fmap go m)

-- -- instance (MonadPlus m) => MonadLogic (ProofStateT ext m) where
-- --     msplit (ProofStateT p) = ProofStateT (go p)
-- --     -- (_ >\\ p)
-- --       where
-- --         go :: Client jdg ext m ext -> Client (Maybe (jdg, ProofStateT ext m jdg)) ext m ext
-- --         go (Request a' fa) = Request (Just (a', ProofStateT $ _)) (go . fa)
-- --         go (Respond b fb') = Respond b (go . fb')
-- --         go (Pure r) = Pure r
-- --         go (M m) = M (fmap go m)
--     -- msplit (ProofStateT (Respond a
--     -- msplit (ProofStateT (Pure r)) = ProofStateT _pure
--     -- msplit (ProofStateT (M m)) = _h

-- instance (MonadPlus m) => MonadPlus (ProofStateT ext m) where
--   mzero = empty
--   mplus = (<|>)

-- instance (MonadThrow m) => MonadThrow (ProofStateT ext m) where
--   throwM e = ProofStateT $ lift $ throwM e

-- instance (MonadCatch m) => MonadCatch (ProofStateT ext m) where
--   catch (ProofStateT m) h = ProofStateT $ catch m (unProofStateT . h)

-- instance (MonadReader env m) => MonadReader env (ProofStateT ext m) where
--   ask = lift ask
--   local f (ProofStateT m) = ProofStateT $ local f m

instance (Monad m) => MonadError err (ProofStateT ext err m) where
    throwError = Failure
    catchError (Subgoal goal k) handle = Subgoal goal (flip catchError handle . k)
    catchError (Effect m) handle = Effect (fmap (flip catchError handle) m)
    -- FIXME: ???
    catchError (Alt p1 p2) handle = _catchAlt
    catchError Empty handle = _catchEmpty
    catchError (Failure err) handle = handle err
    catchError (Axiom e) handle = (Axiom e)

instance (MonadReader r m) => MonadReader r (ProofStateT ext err m) where
    ask = lift ask
    local f (Subgoal goal k) = Subgoal goal (local f . k)
    local f (Effect m) = Effect (local f m)
    local f (Alt p1 p2) = Alt (local f p1) (local f p2)
    local f Empty = Empty
    local f (Failure err) = (Failure err)
    local f (Axiom e) = (Axiom e)

instance (MonadState s m) => MonadState s (ProofStateT ext err m) where
  get = lift get
  put = lift . put

-- axiom :: (Monad m) => ext -> ProofStateT ext m jdg
-- axiom e = ProofStateT $ return e

-- mapExtract :: (Monad m) => (ext -> ext') -> (ext' -> ext) -> ProofStateT ext m jdg -> ProofStateT ext' m jdg
-- mapExtract into out p = ProofStateT $ fmap into ((\j ->  fmap out $ request j) >\\ (unProofStateT p))
