{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}
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
where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Catch hiding (handle)
import           Control.Monad.Except
import qualified Control.Monad.Writer.Lazy as LW
import qualified Control.Monad.Writer.Strict as SW
import           Control.Monad.State
import           Control.Monad.Logic
import           Control.Monad.Morph
import           Control.Monad.Reader

import           GHC.Generics

data ProofStateT ext' ext err s m goal
    = Subgoal goal (ext' -> ProofStateT ext' ext err s m goal)
    | Effect (m (ProofStateT ext' ext err s m goal))
    | Stateful (s -> (s, ProofStateT ext' ext err s m goal))
    | Alt (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
    | Interleave (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
    | Commit (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
    | Empty
    | Failure err
    | Axiom ext
    deriving stock (Generic)

instance (Show goal, Show err, Show ext, Show (m (ProofStateT ext' ext err s m goal))) => Show (ProofStateT ext' ext err s m goal) where
  show (Subgoal goal _) = "(Subgoal " <> show goal <> " <k>)"
  show (Effect m) = "(Effect " <> show m <> ")"
  show (Stateful _) = "(Stateful <s>)"
  show (Alt p1 p2) = "(Alt " <> show p1 <> " " <> show p2 <> ")"
  show (Interleave p1 p2) = "(Interleave " <> show p1 <> " " <> show p2 <> ")"
  show (Commit p1 p2) = "(Commit " <> show p1 <> " " <> show p2 <> ")"
  show Empty = "Empty"
  show (Failure err) = "(Failure " <> show err <> ")"
  show (Axiom ext) = "(Axiom " <> show ext <> ")"

instance Functor m => Functor (ProofStateT ext' ext err s m) where
    fmap f (Subgoal goal k) = Subgoal (f goal) (fmap f . k)
    fmap f (Effect m) = Effect (fmap (fmap f) m)
    fmap f (Stateful s) = Stateful $ fmap (fmap f) . s
    fmap f (Alt p1 p2) = Alt (fmap f p1) (fmap f p2)
    fmap f (Interleave p1 p2) = Interleave (fmap f p1) (fmap f p2)
    fmap f (Commit p1 p2) = Commit (fmap f p1) (fmap f p2)
    fmap _ Empty = Empty
    fmap _ (Failure err) = Failure err
    fmap _ (Axiom ext) = Axiom ext

instance Functor m => Applicative (ProofStateT ext ext err s m) where
    pure = return
    (<*>) = ap

instance MFunctor (ProofStateT ext' ext err s) where
  hoist nat (Subgoal a k) = Subgoal a $ fmap (hoist nat) k
  hoist nat (Effect m)    = Effect $ nat $ fmap (hoist nat) m
  hoist nat (Stateful f)    = Stateful $ fmap (hoist nat) . f
  hoist nat (Alt p1 p2)   = Alt (hoist nat p1) (hoist nat p2)
  hoist nat (Interleave p1 p2)   = Interleave (hoist nat p1) (hoist nat p2)
  hoist nat (Commit p1 p2)   = Commit (hoist nat p1) (hoist nat p2)
  hoist _ (Failure err) = Failure err
  hoist _ Empty         = Empty
  hoist _ (Axiom ext)   = Axiom ext

applyCont
    :: (Functor m)
    => (ext -> ProofStateT ext' ext err s m a)
    -> ProofStateT ext' ext err s m a
    -> ProofStateT ext' ext err s m a
applyCont k (Subgoal goal k') = Subgoal goal (applyCont k . k')
applyCont k (Effect m) = Effect (fmap (applyCont k) m)
applyCont k (Stateful s) = Stateful $ fmap (applyCont k) . s
applyCont k (Alt p1 p2) = Alt (applyCont k p1) (applyCont k p2)
applyCont k (Interleave p1 p2) = Interleave (applyCont k p1) (applyCont k p2)
applyCont k (Commit p1 p2) = Commit (applyCont k p1) (applyCont k p2)
applyCont _ Empty = Empty
applyCont _ (Failure err) = (Failure err)
applyCont k (Axiom ext) = k ext

instance Functor m => Monad (ProofStateT ext ext err s m) where
    return goal = Subgoal goal Axiom
    (Subgoal a k) >>= f = applyCont ((>>= f) . k) (f a)
    (Effect m)    >>= f = Effect (fmap (>>= f) m)
    (Stateful s)  >>= f = Stateful $ fmap (>>= f) . s
    (Alt p1 p2)   >>= f = Alt (p1 >>= f) (p2 >>= f)
    (Interleave p1 p2)   >>= f = Interleave (p1 >>= f) (p2 >>= f)
    (Commit p1 p2)   >>= f = Commit (p1 >>= f) (p2 >>= f)
    (Failure err) >>= _ = Failure err
    Empty         >>= _ = Empty
    (Axiom ext)   >>= _ = Axiom ext

instance MonadTrans (ProofStateT ext ext err s) where
    lift m = Effect (fmap pure m)

instance (Monad m) => Alternative (ProofStateT ext ext err s m) where
    empty = Empty
    (<|>) = Alt

instance (Monad m) => MonadPlus (ProofStateT ext ext err s m) where
    mzero = empty
    mplus = (<|>)

class (Monad m) => MonadExtract ext m | m -> ext where
  -- | Generates a "hole" of type @ext@, which should represent
  -- an incomplete extract.
  hole :: m ext
  default hole :: (MonadTrans t, MonadExtract ext m1, m ~ t m1) => m ext
  hole = lift hole

instance (MonadExtract ext m) => MonadExtract ext (ReaderT r m)
instance (MonadExtract ext m) => MonadExtract ext (StateT s m)
instance (MonadExtract ext m, Monoid w) => MonadExtract ext (LW.WriterT w m)
instance (MonadExtract ext m, Monoid w) => MonadExtract ext (SW.WriterT w m)
instance (MonadExtract ext m) => MonadExtract ext (ExceptT err m)

proofs :: forall ext err s m goal. (MonadExtract ext m) => s -> ProofStateT ext ext err s m goal -> m [Either err (ext, [goal])]
proofs s p = go s [] p
    where
      go s goals (Subgoal goal k) = do
         h <- hole
         (go s (goals ++ [goal]) $ k h)
      go s goals (Effect m) = go s goals =<< m
      go s goals (Stateful f) =
          let (s', p) = f s
          in go s' goals p
      go s goals (Alt p1 p2) = liftA2 (<>) (go s goals p1) (go s goals p2)
      go s goals (Interleave p1 p2) = liftA2 (interleave) (go s goals p1) (go s goals p2)
      go s goals (Commit p1 p2) = go s goals p1 >>= \case
          [] -> go s goals p2
          solns -> pure solns
      go _ _ Empty = pure []
      go _ _ (Failure err) = pure [throwError err]
      go _ goals (Axiom ext) = pure [Right (ext, goals)]

accumEither :: (Semigroup a, Semigroup b) => Either a b -> Either a b -> Either a b
accumEither (Left a1) (Left a2)   = Left (a1 <> a2)
accumEither (Right b1) (Right b2) = Right (b1 <> b2)
accumEither Left{} x              = x
accumEither x Left{}              = x

instance (MonadIO m) => MonadIO (ProofStateT ext ext err s m) where
  liftIO = lift . liftIO

instance (MonadThrow m) => MonadThrow (ProofStateT ext ext err s m) where
  throwM = lift . throwM

instance (MonadCatch m) => MonadCatch (ProofStateT ext ext err s m) where
    catch (Subgoal goal k) handle = Subgoal goal (flip catch handle . k)
    catch (Effect m) handle = Effect . catch m $ pure . handle
    catch (Stateful s) handle = Stateful (fmap (flip catch handle) . s)
    catch (Alt p1 p2) handle = Alt (catch p1 handle) (catch p2 handle)
    catch (Interleave p1 p2) handle = Interleave (catch p1 handle) (catch p2 handle)
    catch (Commit p1 p2) handle = Commit (catch p1 handle) (catch p2 handle)
    catch Empty _ = Empty
    catch (Failure err) _ = Failure err
    catch (Axiom e) _ = (Axiom e)

instance (Monad m) => MonadError err (ProofStateT ext ext err s m) where
    throwError = Failure
    catchError (Subgoal goal k) handle = Subgoal goal (flip catchError handle . k)
    catchError (Effect m) handle = Effect (fmap (flip catchError handle) m)
    catchError (Stateful s) handle = Stateful $ fmap (flip catchError handle) . s
    catchError (Alt p1 p2) handle = catchError p1 handle <|> catchError p2 handle
    catchError (Interleave p1 p2) handle = Interleave (catchError p1 handle) (catchError p2 handle)
    catchError (Commit p1 p2) handle = catchError p1 handle <|> catchError p2 handle
    catchError Empty _ = Empty
    catchError (Failure err) handle = handle err
    catchError (Axiom e) _ = (Axiom e)

instance (MonadReader r m) => MonadReader r (ProofStateT ext ext err s m) where
    ask = lift ask
    local f (Subgoal goal k) = Subgoal goal (local f . k)
    local f (Effect m) = Effect (local f m)
    local f (Stateful s) = Stateful (fmap (local f) . s)
    local f (Alt p1 p2) = Alt (local f p1) (local f p2)
    local f (Interleave p1 p2) = Interleave (local f p1) (local f p2)
    local f (Commit p1 p2) = Commit (local f p1) (local f p2)
    local _ Empty = Empty
    local _ (Failure err) = (Failure err)
    local _ (Axiom e) = (Axiom e)

instance (Monad m) => MonadState s (ProofStateT ext ext err s m) where
    state f = Stateful $ \s ->
      let (a, s') = f s
      in (s', pure a)

axiom :: ext -> ProofStateT ext' ext err s m jdg
axiom = Axiom

subgoals :: (Functor m) => [jdg -> ProofStateT ext ext err s m jdg] -> ProofStateT ext ext err s m jdg  -> ProofStateT ext ext err s m jdg
subgoals [] (Subgoal goal k) = applyCont k (pure goal)
subgoals (f:fs) (Subgoal goal k)  = applyCont (subgoals fs . k) (f goal)
subgoals fs (Effect m) = Effect (fmap (subgoals fs) m)
subgoals fs (Stateful s) = Stateful (fmap (subgoals fs) . s)
subgoals fs (Alt p1 p2) = Alt (subgoals fs p1) (subgoals fs p2)
subgoals fs (Interleave p1 p2) = Interleave (subgoals fs p1) (subgoals fs p2)
subgoals fs (Commit p1 p2) = Commit (subgoals fs p1) (subgoals fs p2)
subgoals _ (Failure err) = Failure err
subgoals _ Empty = Empty
subgoals _ (Axiom ext) = Axiom ext

mapExtract :: (Functor m) => (ext -> ext') -> (ext' -> ext) -> ProofStateT ext ext err s m jdg -> ProofStateT ext' ext' err s m jdg
mapExtract into out = \case
    Subgoal goal k -> Subgoal goal $ mapExtract into out . k . out
    Effect m -> Effect (fmap (mapExtract into out) m)
    Stateful s -> Stateful (fmap (mapExtract into out) . s)
    Alt t1 t2 -> Alt (mapExtract into out t1) (mapExtract into out t2)
    Interleave t1 t2 -> Interleave (mapExtract into out t1) (mapExtract into out t2)
    Commit t1 t2 -> Commit (mapExtract into out t1) (mapExtract into out t2)
    Empty -> Empty
    Failure err -> Failure err
    Axiom ext -> Axiom $ into ext

annotate :: (Functor m) => ([ext'] -> ext -> ext') -> (ext' -> ext) -> ProofStateT ext ext err s m jdg -> ProofStateT ext' ext' err s m jdg
annotate ann out = go []
    where
      go exts (Subgoal goal k) = Subgoal goal (\ext -> go (exts ++ [ext]) $ (k $ out ext))
      go exts (Effect m) = Effect (fmap (go exts) m)
      go exts (Stateful s) = Stateful (fmap (go exts) . s)
      go exts (Alt t1 t2) = Alt (go exts t1) (go exts t2)
      go exts (Interleave t1 t2) = Interleave (go exts t1) (go exts t2)
      go exts (Commit t1 t2) = Commit (go exts t1) (go exts t2)
      go _ Empty = Empty
      go _ (Failure err) = Failure err
      go exts (Axiom ext) = Axiom $ ann exts ext

mapExtract' :: Functor m => (a -> b) -> ProofStateT ext' a err s m jdg -> ProofStateT ext' b err s m jdg
mapExtract' into = \case
    Subgoal goal k -> Subgoal goal $ mapExtract' into . k
    Effect m -> Effect (fmap (mapExtract' into) m)
    Stateful s -> Stateful (fmap (mapExtract' into) . s)
    Alt t1 t2 -> Alt (mapExtract' into t1) (mapExtract' into t2)
    Interleave t1 t2 -> Interleave (mapExtract' into t1) (mapExtract' into t2)
    Commit t1 t2 -> Commit (mapExtract' into t1) (mapExtract' into t2)
    Empty -> Empty
    Failure err -> Failure err
    Axiom ext -> Axiom $ into ext
