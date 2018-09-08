{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
module Refinery.Tactic
  (
    Tactic , identity
  , compose
  , all
  , each
  , (<..>)
  , orElse
  , try
  , many
  , TacticT
  , subgoal
  , tactic
  , solve
  ) where

import           Prelude                          hiding (all)

import           Control.Applicative hiding (many)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Traversable

import           Refinery.MetaSubst
import           Refinery.Proof
import           Refinery.Telescope               (Telescope, (@>))
import qualified Refinery.Telescope               as Tl

newtype Tactic ext jdg m = Tactic { unTactic :: jdg -> m (ProofState ext jdg) }

newtype MultiTactic ext jdg m = MultiTactic { unMultiTactic :: ProofState ext jdg -> m (ProofState ext jdg) }

identity :: (Monad m) => Tactic ext jdg m
identity = Tactic $ return . Unsolved

compose :: (Monad m) => Tactic ext jdg m -> MultiTactic ext jdg m -> Tactic ext jdg m
compose (Tactic t) (MultiTactic mt) = Tactic $ mt <=< t


all :: (Monad m) => Tactic ext jdg m -> MultiTactic ext jdg m
all t = MultiTactic $ fmap join . traverse (unTactic t)

instance (Monad m) => Semigroup (Tactic ext jdg m) where
  t1 <> t2 = t1 `compose` (all t2)

instance (Monad m) => Monoid (Tactic ext jdg m) where
  mempty = identity

each :: (Monad m) => [Tactic ext jdg m] -> MultiTactic ext jdg m
each ts = MultiTactic $ fmap (join . snd) . mapAccumLM applyTac ts
  where
    applyTac (Tactic t:ts) j = (ts,) <$> t j
    applyTac [] j            = return ([], Unsolved j)

(<..>) :: (Monad m) => Tactic ext jdg m -> [Tactic ext jdg m] -> Tactic ext jdg m
t1 <..> ts = t1 `compose` (each ts)

orElse :: (MonadPlus m) => Tactic ext jdg m -> Tactic ext jdg m -> Tactic ext jdg m
orElse (Tactic t) (Tactic t') = Tactic $ \j -> (t j) `mplus` (t' j)

many :: (MonadPlus m) => Tactic ext jdg m -> Tactic ext jdg m
many t = try (t <> many t)

try :: (MonadPlus m) => Tactic ext jdg m -> Tactic ext jdg m
try t = t `orElse` identity

newtype TacticT ext jdg err m a = TacticT { unTacticT :: WriterT (Telescope ext (ProofState ext jdg)) (ExceptT err m) a }
  deriving
    ( Functor , Applicative, Monad
    , Alternative, MonadPlus
    , MonadError err, MonadWriter (Telescope ext (ProofState ext jdg)), MonadState s
    )

instance MonadTrans (TacticT ext jdg err) where
  lift = TacticT . lift . lift

runTacticT = runExceptT . runWriterT . unTacticT

subgoal :: (MetaSubst ext ext m) => jdg -> TacticT ext jdg err m (MetaVar ext)
subgoal j = do
  x <- lift $ fresh 
  tell (Tl.singleton x (Unsolved j))
  return x

tactic :: (Monad m) => (jdg -> TacticT ext jdg err m ext) -> Tactic ext jdg m
tactic t = Tactic $ \j -> runTacticT (t j) >>= \case
  Left err -> fail "Tactic Error!"
  Right (ext, goals) -> return $ Subgoals goals ext

solve :: (Monad m) => Tactic ext jdg m -> jdg -> m (ProofState ext jdg)
solve (Tactic t) j = t j
