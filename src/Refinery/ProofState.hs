{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

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
{-# LANGUAGE RankNTypes #-}
module Refinery.ProofState
where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Catch hiding (handle)
import           Control.Monad.Except
import qualified Control.Monad.Writer.Lazy as LW
import qualified Control.Monad.Writer.Strict as SW
import           Control.Monad.State
import           Control.Monad.Morph
import           Control.Monad.Reader
import           Data.List

import           GHC.Generics

-- | The core data type of the library.
-- This represents a reified, in-progress proof strategy for a particular goal.
--
-- NOTE: We need to split up the extract type into @ext'@ and @ext@, as
-- we want to be functorial (and monadic) in @ext@, but it shows up in both
-- co and contravariant positions. Splitting the type variable up into two solves this problem,
-- at the cost of looking ugly.
data ProofStateT ext' ext err s m goal
    = Subgoal goal (ext' -> ProofStateT ext' ext err s m goal)
    -- ^ Represents a subgoal, and a continuation that tells
    -- us what to do with the resulting extract.
    | Effect (m (ProofStateT ext' ext err s m goal))
    -- ^ Run an effect.
    | Stateful (s -> (s, ProofStateT ext' ext err s m goal))
    -- ^ Run a stateful computation. We don't want to use 'StateT' here, as it
    -- doesn't play nice with backtracking.
    | Alt (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
    -- ^ Combine together the results of two @ProofState@s.
    | Interleave (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
    -- ^ Similar to 'Alt', but will interleave the results, rather than just appending them.
    -- This is useful if the first argument produces potentially infinite results.
    | Empty
    -- ^ Silent failure. Always causes a backtrack, unlike 'Failure'.
    | Failure err (ext' -> ProofStateT ext' ext err s m goal)
    -- ^ This does double duty, depending on whether or not the user calls 'proofs'
    -- or 'partialProofs'. In the first case, we ignore the continutation, backtrack, and
    -- return an error in the result of 'proofs'.
    -- In the second, we treat this as a sort of "unsolvable subgoal", and call the
    -- continuation with a hole.
    | Axiom ext
    -- ^ Represents a simple extract.
    deriving stock (Generic)

instance (Show goal, Show err, Show ext, Show (m (ProofStateT ext' ext err s m goal))) => Show (ProofStateT ext' ext err s m goal) where
  show (Subgoal goal _) = "(Subgoal " <> show goal <> " <k>)"
  show (Effect m) = "(Effect " <> show m <> ")"
  show (Stateful _) = "(Stateful <s>)"
  show (Alt p1 p2) = "(Alt " <> show p1 <> " " <> show p2 <> ")"
  show (Interleave p1 p2) = "(Interleave " <> show p1 <> " " <> show p2 <> ")"
  show Empty = "Empty"
  show (Failure err _) = "(Failure " <> show err <> " <k>)"
  show (Axiom ext) = "(Axiom " <> show ext <> ")"

instance Functor m => Functor (ProofStateT ext' ext err s m) where
    fmap f (Subgoal goal k) = Subgoal (f goal) (fmap f . k)
    fmap f (Effect m) = Effect (fmap (fmap f) m)
    fmap f (Stateful s) = Stateful $ fmap (fmap f) . s
    fmap f (Alt p1 p2) = Alt (fmap f p1) (fmap f p2)
    fmap f (Interleave p1 p2) = Interleave (fmap f p1) (fmap f p2)
    fmap _ Empty = Empty
    fmap f (Failure err k) = Failure err (fmap f . k)
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
  hoist nat (Failure err k) = Failure err $ fmap (hoist nat) k
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
applyCont _ Empty = Empty
applyCont k (Failure err k') = Failure err (applyCont k . k')
applyCont k (Axiom ext) = k ext

instance Functor m => Monad (ProofStateT ext ext err s m) where
    return goal = Subgoal goal Axiom
    (Subgoal a k) >>= f = applyCont (f <=< k) (f a)
    (Effect m)    >>= f = Effect (fmap (>>= f) m)
    (Stateful s)  >>= f = Stateful $ fmap (>>= f) . s
    (Alt p1 p2)   >>= f = Alt (p1 >>= f) (p2 >>= f)
    (Interleave p1 p2)   >>= f = Interleave (p1 >>= f) (p2 >>= f)
    (Failure err k) >>= f = Failure err (f <=< k)
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

class (Monad m) => MonadExtract ext err m | m -> ext, m -> err where
  -- | Generates a "hole" of type @ext@, which should represent
  -- an incomplete extract.
  hole :: m ext
  default hole :: (MonadTrans t, MonadExtract ext err m1, m ~ t m1) => m ext
  hole = lift hole

  -- | Generates an "unsolvable hole" of type @err@, which should represent
  -- an incomplete extract that we have no hope of solving.
  --
  -- These will get generated when you generate partial extracts via 'runPartialTacticT'.
  unsolvableHole :: err -> m ext
  default unsolvableHole :: (MonadTrans t, MonadExtract ext err m1, m ~ t m1) => err -> m ext
  unsolvableHole = lift . unsolvableHole
  -- default hole :: (MonadTrans t, MonadExtract ext m1, m ~ t m1) => m ext
  -- hole = lift hole

instance (MonadExtract ext err m) => MonadExtract ext err (ReaderT r m)
instance (MonadExtract ext err m) => MonadExtract ext err (StateT s m)
instance (MonadExtract ext err m, Monoid w) => MonadExtract ext err (LW.WriterT w m)
instance (MonadExtract ext err m, Monoid w) => MonadExtract ext err (SW.WriterT w m)
instance (MonadExtract ext err m) => MonadExtract ext err (ExceptT err m)

data Proof ext s goal = Proof { pf_extract :: ext, pf_state :: s, pf_unsolvedGoals :: [goal] }
    deriving (Eq, Show, Generic)

interleave :: [a] -> [a] -> [a]
interleave (x : xs) (y : ys) = x : y : (interleave xs ys)
interleave xs [] = xs
interleave [] ys = ys

prioritizing :: (forall a. [a] -> [a] -> [a])
             -> Either [b] [c]
             -> Either [b] [c]
             -> Either [b] [c]
prioritizing combine (Left a1) (Left a2)   = Left $ a1 `combine` a2
prioritizing _ (Left _) (Right b2)         = Right b2
prioritizing _ (Right b1) (Left _)         = Right b1
prioritizing combine (Right b1) (Right b2) = Right $ b1 `combine` b2

-- | Interpret a 'ProofStateT' into a list of (possibly incomplete) extracts.
-- This function will cause a proof to terminate when it encounters a 'Failure', and will return a 'Left'.
-- If you want to still recieve an extract even when you encounter a failure, you should use 'partialProofs'.
proofs :: forall ext err s m goal. (MonadExtract ext err m) => s -> ProofStateT ext ext err s m goal -> m (Either [err] [(Proof ext s goal)])
proofs s p = go s [] p
    where
      go :: s -> [goal] -> ProofStateT ext ext err s m goal -> m (Either [err] [Proof ext s goal])
      go s goals (Subgoal goal k) = do
         h <- hole
         (go s (goals ++ [goal]) $ k h)
      go s goals (Effect m) = go s goals =<< m
      go s goals (Stateful f) =
          let (s', p) = f s
          in go s' goals p
      go s goals (Alt p1 p2) = liftA2 (prioritizing (<>)) (go s goals p1) (go s goals p2)
      go s goals (Interleave p1 p2) = liftA2 (prioritizing interleave) (go s goals p1) (go s goals p2)
      go _ _ Empty = pure $ Left []
      go _ _ (Failure err _) = pure $ Left [err]
      go s goals (Axiom ext) = pure $ Right $ [Proof ext s goals]

-- | The result of executing 'partialProofs'.
data PartialProof ext s goal err
    = PartialProof ext s [goal] [err]
    -- ^ A so called "partial proof". These are proofs that encountered errors
    -- during execution.
    deriving (Eq, Show, Generic)

-- | Interpret a 'ProofStateT' into a list of (possibly incomplete) extracts.
-- This function will continue producing an extract when it encounters a 'Failure', leaving
-- a hole in the extract in it's place. If you want the extraction to terminate when you encounter an error,
-- you should use 'proofs'.
--
-- This function will return all the 'SuccessfulProof' before the 'PartialProof'.
partialProofs :: forall ext err s m goal. (MonadExtract ext err m) => s -> ProofStateT ext ext err s m goal -> m (Either [PartialProof ext s goal err] [Proof ext s goal])
partialProofs s pf = go s [] [] pf
    where
      go :: s -> [goal] -> [err] -> ProofStateT ext ext err s m goal -> m (Either [PartialProof ext s goal err] [Proof ext s goal])
      go s goals errs (Subgoal goal k) = do
         h <- hole
         go s (goals ++ [goal]) errs $ k h
      go s goals errs (Effect m) = go s goals errs =<< m
      go s goals errs (Stateful f) =
          let (s', p) = f s
          in go s' goals errs p
      go s goals errs (Alt p1 p2) = liftA2 (prioritizing (<>)) (go s goals errs p1) (go s goals errs p2)
      go s goals errs (Interleave p1 p2) = liftA2 (prioritizing interleave) (go s goals errs p1) (go s goals errs p2)
      go _ _ _ Empty = pure $ Left []
      go s goals errs (Failure err k) = do
          h <- unsolvableHole err
          go s goals (errs ++ [err]) $ k h
      go s goals [] (Axiom ext) = pure $ Right [Proof ext s goals]
      go s goals errs (Axiom ext) = pure $ Left [PartialProof ext s goals errs]

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
    catch Empty _ = Empty
    catch (Failure err k) handle = Failure err (flip catch handle . k)
    catch (Axiom e) _ = (Axiom e)

 -- FIXME: Does catching errors even make sense????
instance (Monad m) => MonadError err (ProofStateT ext ext err s m) where
    throwError err = Failure err Axiom
    catchError (Subgoal goal k) handle = Subgoal goal (flip catchError handle . k)
    catchError (Effect m) handle = Effect (fmap (flip catchError handle) m)
    catchError (Stateful s) handle = Stateful $ fmap (flip catchError handle) . s
    catchError (Alt p1 p2) handle = catchError p1 handle <|> catchError p2 handle
    catchError (Interleave p1 p2) handle = Interleave (catchError p1 handle) (catchError p2 handle)
    catchError Empty _ = Empty
    catchError (Failure err k) handle = applyCont (flip catchError handle . k) $ handle err
    catchError (Axiom e) _ = Axiom e

instance (MonadReader r m) => MonadReader r (ProofStateT ext ext err s m) where
    ask = lift ask
    local f (Subgoal goal k) = Subgoal goal (local f . k)
    local f (Effect m) = Effect (local f m)
    local f (Stateful s) = Stateful (fmap (local f) . s)
    local f (Alt p1 p2) = Alt (local f p1) (local f p2)
    local f (Interleave p1 p2) = Interleave (local f p1) (local f p2)
    local _ Empty = Empty
    local f (Failure err k) = Failure err (local f . k)
    local _ (Axiom e) = Axiom e

instance (Monad m) => MonadState s (ProofStateT ext ext err s m) where
    state f = Stateful $ \s ->
      let (a, s') = f s
      in (s', pure a)

{-# DEPRECATED axiom "Use Axiom instead" #-}
axiom :: ext -> ProofStateT ext' ext err s m jdg
axiom = Axiom

-- | @subgoals fs p@ will apply a list of functions producing a new 'ProofState' to each of the subgoals of @p@.
-- If the list of functions is longer than the number of subgoals, then the extra functions are ignored.
-- If the list of functions is shorter, then we simply apply @pure@ to all of the remaining subgoals.
subgoals :: (Functor m) => [jdg -> ProofStateT ext ext err s m jdg] -> ProofStateT ext ext err s m jdg  -> ProofStateT ext ext err s m jdg
subgoals [] (Subgoal goal k) = applyCont k (pure goal)
subgoals (f:fs) (Subgoal goal k)  = applyCont (subgoals fs . k) (f goal)
subgoals fs (Effect m) = Effect (fmap (subgoals fs) m)
subgoals fs (Stateful s) = Stateful (fmap (subgoals fs) . s)
subgoals fs (Alt p1 p2) = Alt (subgoals fs p1) (subgoals fs p2)
subgoals fs (Interleave p1 p2) = Interleave (subgoals fs p1) (subgoals fs p2)
subgoals fs (Failure err k) = Failure err (subgoals fs . k)
subgoals _ Empty = Empty
subgoals _ (Axiom ext) = Axiom ext

mapExtract :: (Functor m) => (ext -> ext') -> (ext' -> ext) -> ProofStateT ext ext err s m jdg -> ProofStateT ext' ext' err s m jdg
mapExtract into out = \case
    Subgoal goal k -> Subgoal goal $ mapExtract into out . k . out
    Effect m -> Effect (fmap (mapExtract into out) m)
    Stateful s -> Stateful (fmap (mapExtract into out) . s)
    Alt t1 t2 -> Alt (mapExtract into out t1) (mapExtract into out t2)
    Interleave t1 t2 -> Interleave (mapExtract into out t1) (mapExtract into out t2)
    Empty -> Empty
    Failure err k -> Failure err $ mapExtract into out . k . out
    Axiom ext -> Axiom $ into ext

mapExtract' :: Functor m => (a -> b) -> ProofStateT ext' a err s m jdg -> ProofStateT ext' b err s m jdg
mapExtract' into = \case
    Subgoal goal k -> Subgoal goal $ mapExtract' into . k
    Effect m -> Effect (fmap (mapExtract' into) m)
    Stateful s -> Stateful (fmap (mapExtract' into) . s)
    Alt t1 t2 -> Alt (mapExtract' into t1) (mapExtract' into t2)
    Interleave t1 t2 -> Interleave (mapExtract' into t1) (mapExtract' into t2)
    Empty -> Empty
    Failure err k -> Failure err $ mapExtract' into . k
    Axiom ext -> Axiom $ into ext
