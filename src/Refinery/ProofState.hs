{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

-----------------------------------------------------------------------------
-- | The datatype that drives both Rules and Tactics
--
-- If you just want to build tactics, you probably want to use 'Refinery.Tactic' instead.
-- However, if you need to get involved in the core of the library, this is the place to start.
--
-- Module      :  Refinery.ProofState
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
--
module Refinery.ProofState where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Catch hiding (handle)
import           Control.Monad.Except
import qualified Control.Monad.Writer.Lazy as LW
import qualified Control.Monad.Writer.Strict as SW
import           Control.Monad.State
import           Control.Monad.Morph
import           Control.Monad.Reader

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
    -- ^ Combine together the results of two @ProofState@s, preserving the order that they were synthesized in.
    | Interleave (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
    -- ^ Similar to 'Alt', but will interleave the results, rather than just appending them.
    -- This is useful if the first argument produces potentially infinite results.
    | Commit (ProofStateT ext' ext err s m goal) (ProofStateT ext' ext err s m goal)
     -- ^ 'Commit' runs the first proofstate, and only runs the second if the first
     -- does not produce any successful results.
    | Empty
    -- ^ Silent failure. Always causes a backtrack, unlike 'Failure'.
    | Failure err (ext' -> ProofStateT ext' ext err s m goal)
    -- ^ This does double duty, depending on whether or not the user calls 'proofs'
    -- or 'partialProofs'. In the first case, we ignore the continutation, backtrack, and
    -- return an error in the result of 'proofs'.
    -- In the second, we treat this as a sort of "unsolvable subgoal", and call the
    -- continuation with a hole.
    | Handle (ProofStateT ext' ext err s m goal) (err -> m err)
    -- ^ An installed error handler. These allow us to add annotations to errors,
    -- or run effects.
    | Axiom ext
    -- ^ Represents a simple extract.
    deriving stock (Generic, Functor)

instance (Show goal, Show err, Show ext, Show (m (ProofStateT ext' ext err s m goal))) => Show (ProofStateT ext' ext err s m goal) where
  show (Subgoal goal _) = "(Subgoal " <> show goal <> " <k>)"
  show (Effect m) = "(Effect " <> show m <> ")"
  show (Stateful _) = "(Stateful <s>)"
  show (Alt p1 p2) = "(Alt " <> show p1 <> " " <> show p2 <> ")"
  show (Interleave p1 p2) = "(Interleave " <> show p1 <> " " <> show p2 <> ")"
  show (Commit p1 p2) = "(Commit " <> show p1 <> " " <> show p2 <> ")"
  show Empty = "Empty"
  show (Failure err _) = "(Failure " <> show err <> " <k>)"
  show (Handle p _) = "(Handle " <> show p <> " <h>)"
  show (Axiom ext) = "(Axiom " <> show ext <> ")"

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
  hoist nat (Failure err k) = Failure err $ fmap (hoist nat) k
  hoist nat (Handle p h) = Handle (hoist nat p) (nat . h)
  hoist _ Empty         = Empty
  hoist _ (Axiom ext)   = Axiom ext

-- | Apply a continuation that creates new proof states from an extract
-- onto all of the 'Axiom' constructors of a 'ProofStateT'.
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
applyCont k (Failure err k') = Failure err (applyCont k . k')
applyCont k (Handle p h) = Handle (applyCont k p) h
applyCont k (Axiom ext) = k ext

instance Functor m => Monad (ProofStateT ext ext err s m) where
    return goal = Subgoal goal Axiom
    (Subgoal a k)      >>= f = applyCont (f <=< k) (f a)
    (Effect m)         >>= f = Effect (fmap (>>= f) m)
    (Stateful s)       >>= f = Stateful $ fmap (>>= f) . s
    (Alt p1 p2)        >>= f = Alt (p1 >>= f) (p2 >>= f)
    (Interleave p1 p2) >>= f = Interleave (p1 >>= f) (p2 >>= f)
    (Commit p1 p2)     >>= f = Commit (p1 >>= f) (p2 >>= f)
    (Failure err k)    >>= f = Failure err (f <=< k)
    (Handle p h)       >>= f = Handle (p >>= f) h
    Empty              >>= _ = Empty
    (Axiom ext)        >>= _ = Axiom ext

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

instance (MonadExtract ext err m) => MonadExtract ext err (ReaderT r m)
instance (MonadExtract ext err m) => MonadExtract ext err (StateT s m)
instance (MonadExtract ext err m, Monoid w) => MonadExtract ext err (LW.WriterT w m)
instance (MonadExtract ext err m, Monoid w) => MonadExtract ext err (SW.WriterT w m)
instance (MonadExtract ext err m) => MonadExtract ext err (ExceptT err m)

-- | Represents a single result of the execution of some tactic.
data Proof s goal ext = Proof
    { pf_extract :: ext
    -- ^ The extract of the tactic.
    , pf_state :: s
    -- ^ The state at the end of tactic execution.
    , pf_unsolvedGoals :: [goal]
    -- ^ All the goals that were still unsolved by the end of tactic execution.
    }
    deriving (Eq, Show, Generic)

-- | Interleave two lists together.
-- @
--     interleave [1,2,3,4] [5,6]
-- @
-- > [1,5,2,6,3,4]
interleave :: [a] -> [a] -> [a]
interleave (x : xs) (y : ys) = x : y : (interleave xs ys)
interleave xs [] = xs
interleave [] ys = ys

-- | Helper function for combining together two results from either 'proofs' or 'partialProofs'.
-- @prioritizing f as bs@ will use @f@ to combine together either two lists of failures or two lists of successes.
-- If we have one list of successes and one list of failures, we always take the successes.
--
-- The logic behind this is that if either 'Alt' or 'Interleave' have successes, then the failures aren't particularly interesting.
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
proofs :: forall ext err s m goal. (MonadExtract ext err m) => s -> ProofStateT ext ext err s m goal -> m (Either [err] [(Proof s goal ext)])
proofs s p = go s [] pure p
    where
      go :: s -> [goal] -> (err -> m err) -> ProofStateT ext ext err s m goal -> m (Either [err] [Proof s goal ext])
      go s goals handlers (Subgoal goal k) = do
         h <- hole
         (go s (goals ++ [goal]) handlers $ k h)
      go s goals handlers (Effect m) = m >>= go s goals handlers
      go s goals handlers (Stateful f) =
          let (s', p) = f s
          in go s' goals handlers p
      go s goals handlers (Alt p1 p2) =
          liftA2 (prioritizing (<>)) (go s goals handlers p1) (go s goals handlers p2)
      go s goals handlers (Interleave p1 p2) =
          liftA2 (prioritizing interleave) (go s goals handlers p1) (go s goals handlers p2)
      go s goals handlers (Commit p1 p2) = go s goals handlers p1 >>= \case
          Right solns | not (null solns) -> pure $ Right solns
          _                              -> go s goals handlers p2
      go _ _ _ Empty = pure $ Left []
      go _ _ handlers (Failure err _) = do
          annErr <- handlers err
          pure $ Left [annErr]
      go s goals handlers (Handle p h) =
          -- NOTE [Handler ordering]:
          -- If we have multiple handlers in scope, then we want the handlers closer to the error site to
          -- run /first/. This allows the handlers up the stack to add their annotations on top of the
          -- ones lower down, which is the behavior that we desire.
          -- IE: for @handler f >> handler g >> failure err@, @g@ ought to be run before @f@.
          go s goals (h >=> handlers) p
      go s goals _ (Axiom ext) = pure $ Right $ [Proof ext s goals]

-- | The result of executing 'partialProofs'.
data PartialProof s err goal ext
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
partialProofs :: forall ext err s m goal. (MonadExtract ext err m) => s -> ProofStateT ext ext err s m goal -> m (Either [PartialProof s err goal ext] [Proof s goal ext])
partialProofs s pf = go s [] [] pure pf
    where
      go :: s -> [goal] -> [err] -> (err -> m err) -> ProofStateT ext ext err s m goal -> m (Either [PartialProof s err goal ext] [Proof s goal ext])
      go s goals errs handlers (Subgoal goal k) = do
         h <- hole
         go s (goals ++ [goal]) errs handlers $ k h
      go s goals errs handlers (Effect m) = m >>= go s goals errs handlers
      go s goals errs handlers (Stateful f) =
          let (s', p) = f s
          in go s' goals errs handlers p
      go s goals errs handlers (Alt p1 p2) = liftA2 (prioritizing (<>)) (go s goals errs handlers p1) (go s goals errs handlers p2)
      go s goals errs handlers (Interleave p1 p2) = liftA2 (prioritizing interleave) (go s goals errs handlers p1) (go s goals errs handlers p2)
      go s goals errs handlers (Commit p1 p2) = go s goals errs handlers p1 >>= \case
          Right solns | not (null solns) -> pure $ Right solns
          _                              -> go s goals errs handlers p2
      go _ _ _ _ Empty = pure $ Left []
      go s goals errs handlers (Failure err k) = do
          annErr <- handlers err
          h <- unsolvableHole annErr
          go s goals (errs ++ [annErr]) handlers $ k h
      go s goals errs handlers (Handle p h) =
          -- See NOTE [Handler ordering]
          go s goals errs (h >=> handlers) p
      go s goals [] _ (Axiom ext) = pure $ Right [Proof ext s goals]
      go s goals errs _ (Axiom ext) = pure $ Left [PartialProof ext s goals errs]

instance (MonadIO m) => MonadIO (ProofStateT ext ext err s m) where
  liftIO = lift . liftIO

instance (MonadThrow m) => MonadThrow (ProofStateT ext ext err s m) where
  throwM = lift . throwM

instance (Monad m) => MonadState s (ProofStateT ext ext err s m) where
    state f = Stateful $ \s ->
      let (a, s') = f s
      in (s', pure a)

{-# DEPRECATED axiom "Use Axiom instead" #-}
axiom :: ext -> ProofStateT ext' ext err s m jdg
axiom = Axiom

-- | @subgoals fs p@ will apply a list of functions producing a new 'ProofState' to each of the subgoals of @p@ in order.
-- If the list of functions is longer than the number of subgoals, then the extra functions are ignored.
-- If the list of functions is shorter, then we simply apply @pure@ to all of the remaining subgoals.
subgoals :: (Functor m) => [jdg -> ProofStateT ext ext err s m jdg] -> ProofStateT ext ext err s m jdg  -> ProofStateT ext ext err s m jdg
subgoals [] (Subgoal goal k) = applyCont k (pure goal)
subgoals (f:fs) (Subgoal goal k)  = applyCont (subgoals fs . k) (f goal)
subgoals fs (Effect m) = Effect (fmap (subgoals fs) m)
subgoals fs (Stateful s) = Stateful (fmap (subgoals fs) . s)
subgoals fs (Alt p1 p2) = Alt (subgoals fs p1) (subgoals fs p2)
subgoals fs (Interleave p1 p2) = Interleave (subgoals fs p1) (subgoals fs p2)
subgoals fs (Commit p1 p2) = Commit (subgoals fs p1) (subgoals fs p2)
subgoals fs (Failure err k) = Failure err (subgoals fs . k)
subgoals fs (Handle p h) = Handle (subgoals fs p) h
subgoals _ Empty = Empty
subgoals _ (Axiom ext) = Axiom ext

-- | @mapExtract f g p@ allows yout to modify the extract type of a ProofState.
-- This witness the @Profunctor@ instance of 'ProofState', which we can't write without a newtype due to
-- the position of the type variables
mapExtract :: (Functor m) => (a -> ext') -> (ext -> b) -> ProofStateT ext' ext err s m jdg -> ProofStateT a b err s m jdg
mapExtract into out (Subgoal goal k) = Subgoal goal (mapExtract into out . k . into)
mapExtract into out (Effect m) = Effect (fmap (mapExtract into out) m)
mapExtract into out (Stateful s) = Stateful (fmap (mapExtract into out) . s)
mapExtract into out (Alt p1 p2) = Alt (mapExtract into out p1) (mapExtract into out p2)
mapExtract into out (Interleave p1 p2) = Interleave (mapExtract into out p1) (mapExtract into out p2)
mapExtract into out (Commit p1 p2) = Commit (mapExtract into out p1) (mapExtract into out p2)
mapExtract _ _ Empty = Empty
mapExtract into out (Failure err k) = Failure err (mapExtract into out . k . into)
mapExtract into out (Handle p h) = Handle (mapExtract into out p) h
mapExtract _ out (Axiom ext) = Axiom (out ext)
