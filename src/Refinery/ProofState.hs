{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Refinery.ProofState
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
module Refinery.ProofState
  -- ( ProofStateT ext'(..)
  -- , axiom
  -- , mapExtract
  -- )
where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Catch hiding (handle)
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Logic
import           Control.Monad.Morph
import           Control.Monad.Reader.Class

import           GHC.Generics

-- import Pipes.Core
-- import Pipes.Internal

-- newtype ProofStateT ext' ext m jdg = ProofStateT ext' { unProofStateT ext' :: Client jdg ext m ext }
data ProofStateT ext' ext err m goal
    = Subgoal goal (ext' -> ProofStateT ext' ext err m goal)
    | Effect (m (ProofStateT ext' ext err m goal))
    | Alt (ProofStateT ext' ext err m goal) (ProofStateT ext' ext err m goal)
    | Empty
    | Failure err
    | Axiom ext
    deriving stock (Generic)

instance (Show goal, Show err, Show ext, Show (m (ProofStateT ext' ext err m goal))) => Show (ProofStateT ext' ext err m goal) where
  show (Subgoal goal _) = "(Subgoal " <> show goal <> " <k>)"
  show (Effect m) = "(Effect " <> show m <> ")"
  show (Alt p1 p2) = "(Alt " <> show p1 <> " " <> show p2 <> ")"
  show Empty = "Empty"
  show (Failure err) = "(Failure " <> show err <> ")"
  show (Axiom ext) = "(Axiom " <> show ext <> ")"

instance Functor m => Functor (ProofStateT ext' ext err m) where
    fmap f (Subgoal goal k) = Subgoal (f goal) (fmap f . k)
    fmap f (Effect m) = Effect (fmap (fmap f) m)
    fmap f (Alt p1 p2) = Alt (fmap f p1) (fmap f p2)
    fmap _ Empty = Empty
    fmap _ (Failure err) = Failure err
    fmap _ (Axiom ext) = Axiom ext

-- TODO Do this right pls
instance Functor m => Applicative (ProofStateT ext ext err m) where
    pure = return
    (<*>) = ap

instance MFunctor (ProofStateT ext' ext err) where
  hoist nat (Subgoal a k) = Subgoal a $ fmap (hoist nat) k
  hoist nat (Effect m)    = Effect $ nat $ fmap (hoist nat) m
  hoist nat (Alt p1 p2)   = Alt (hoist nat p1) (hoist nat p2)
  hoist _ (Failure err) = Failure err
  hoist _ Empty         = Empty
  hoist _ (Axiom ext)   = Axiom ext

applyCont
    :: (Functor m)
    => (ext -> ProofStateT ext ext err m a)
    -> ProofStateT ext ext err m a
    -> ProofStateT ext ext err m a
applyCont k (Subgoal goal k') = Subgoal goal (applyCont k . k')
applyCont k (Effect m) = Effect (fmap (applyCont k) m)
applyCont k (Alt p1 p2) = Alt (applyCont k p1) (applyCont k p2)
applyCont _ Empty = Empty
applyCont _ (Failure err) = (Failure err)
applyCont k (Axiom ext) = k ext

instance Functor m => Monad (ProofStateT ext ext err m) where
    return goal = Subgoal goal Axiom
    (Subgoal a k) >>= f = applyCont ((>>= f) . k) (f a)
    (Effect m)    >>= f = Effect (fmap (>>= f) m)
    (Alt p1 p2)   >>= f = Alt (p1 >>= f) (p2 >>= f)
    (Failure err) >>= _ = Failure err
    Empty         >>= _ = Empty
    (Axiom ext)   >>= _ = Axiom ext

instance MonadTrans (ProofStateT ext ext err) where
    lift m = Effect (fmap pure m)

instance (Monad m) => Alternative (ProofStateT ext ext err m) where
    empty = Empty
    (<|>) = Alt

instance (Monad m) => MonadPlus (ProofStateT ext ext err m) where
    mzero = empty
    mplus = (<|>)

instance (Monad m) => MonadLogic (ProofStateT ext ext err m) where
    msplit (Subgoal goal k) = Subgoal (Just (goal, Empty)) (msplit . k)
    msplit (Effect m)       = Effect (fmap msplit m)
    msplit (Alt p1 p2)      = msplit p1 >>= \case
        Just (a, rest) -> pure $ Just (a, rest <|> p2)
        Nothing        -> msplit p2
    msplit Empty            = pure Nothing
    msplit (Failure _)    = pure Nothing
    msplit (Axiom _)      = pure Nothing

class (Monad m) => MonadExtract ext m | m -> ext where
  -- | Generates a "hole" of type @ext@, which should represent
  -- an incomplete extract.
  hole :: m ext
  default hole :: (MonadTrans t, MonadExtract ext m1, m ~ t m1) => m ext
  hole = lift hole

-- TODO [Reed] Add the rest of the instances
instance (MonadExtract ext m) => MonadExtract ext (StateT s m)
instance (MonadExtract ext m) => MonadExtract ext (ExceptT err m)

proofs :: (Monoid err, MonadExtract ext m) => ProofStateT ext ext err m goal -> m (Either err (ext, [goal]))
proofs p = runExceptT $ runStateT (proofs' p) []

-- TODO [Reed] Use a dlist
proofs'
    :: (Monoid err, MonadExtract ext m)
    => ProofStateT ext ext err m goal
    -> StateT [goal] (ExceptT err m) ext
proofs' (Subgoal goal k) = do
    h <- hole
    modify (++ [goal])
    proofs' $ k h
proofs' (Effect m)       = proofs' =<< (lift $ lift m)
proofs' (Alt p1 p2)      = (proofs' p1) `catchError` (\_ -> proofs' p2)
proofs' Empty            = throwError mempty
proofs' (Failure err)    = throwError err
proofs' (Axiom ext)      = pure ext

accumEither :: (Semigroup a, Semigroup b) => Either a b -> Either a b -> Either a b
accumEither (Left a1) (Left a2)   = Left (a1 <> a2)
accumEither (Right b1) (Right b2) = Right (b1 <> b2)
accumEither Left{} x              = x
accumEither x Left{}              = x

instance (MonadIO m) => MonadIO (ProofStateT ext ext err m) where
  liftIO = lift . liftIO

instance (MonadThrow m) => MonadThrow (ProofStateT ext ext err m) where
  throwM = lift . throwM

instance (MonadCatch m) => MonadCatch (ProofStateT ext ext err m) where
    catch (Subgoal goal k) handle = Subgoal goal (flip catch handle . k)
    catch (Effect m) handle = Effect . catch m $ pure . handle
    catch (Alt p1 p2) handle = catch p1 handle <|> catch p2 handle
    catch Empty _ = Empty
    catch (Failure err) _ = Failure err
    catch (Axiom e) _ = (Axiom e)


instance (Monad m) => MonadError err (ProofStateT ext ext err m) where
    throwError = Failure
    catchError (Subgoal goal k) handle = Subgoal goal (flip catchError handle . k)
    catchError (Effect m) handle = Effect (fmap (flip catchError handle) m)
    catchError (Alt p1 p2) handle = catchError p1 handle <|> catchError p2 handle
    catchError Empty _ = Empty
    catchError (Failure err) handle = handle err
    catchError (Axiom e) _ = (Axiom e)

instance (MonadReader r m) => MonadReader r (ProofStateT ext ext err m) where
    ask = lift ask
    local f (Subgoal goal k) = Subgoal goal (local f . k)
    local f (Effect m) = Effect (local f m)
    local f (Alt p1 p2) = Alt (local f p1) (local f p2)
    local _ Empty = Empty
    local _ (Failure err) = (Failure err)
    local _ (Axiom e) = (Axiom e)

instance (MonadState s m) => MonadState s (ProofStateT ext ext err m) where
  get = lift get
  put = lift . put

axiom :: ext -> ProofStateT ext' ext err m jdg
axiom = Axiom

subgoals :: (Functor m) => [jdg -> ProofStateT ext ext err m jdg] -> ProofStateT ext ext err m jdg  -> ProofStateT ext ext err m jdg
subgoals [] (Subgoal goal k) = applyCont k (pure goal)
subgoals (f:fs) (Subgoal goal k)  = applyCont (subgoals fs . k) (f goal)
subgoals fs (Effect m) = Effect (fmap (subgoals fs) m)
subgoals fs (Alt p1 p2) = Alt (subgoals fs p1) (subgoals fs p2)
subgoals _ (Failure err) = Failure err
subgoals _ Empty = Empty
subgoals _ (Axiom ext) = Axiom ext

mapExtract :: (Functor m) => (ext -> ext') -> (ext' -> ext) -> ProofStateT ext ext err m jdg -> ProofStateT ext' ext' err m jdg
mapExtract into out = \case
    Subgoal goal k -> Subgoal goal $ mapExtract into out . k . out
    Effect m -> Effect (fmap (mapExtract into out) m)
    Alt t1 t2 -> Alt (mapExtract into out t1) (mapExtract into out t2)
    Empty -> Empty
    Failure err -> Failure err
    Axiom ext -> Axiom $ into ext

mapExtract' :: Functor m => (a -> b) -> ProofStateT ext' a err m jdg -> ProofStateT ext' b err m jdg
mapExtract' into = \case
    Subgoal goal k -> Subgoal goal $ mapExtract' into . k
    Effect m -> Effect (fmap (mapExtract' into) m)
    Alt t1 t2 -> Alt (mapExtract' into t1) (mapExtract' into t2)
    Empty -> Empty
    Failure err -> Failure err
    Axiom ext -> Axiom $ into ext

