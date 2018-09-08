{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UndecidableInstances       #-}
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

import           Prelude                     hiding (all)

import           Control.Applicative         hiding (many)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Traversable.Extensions

import           Refinery.MetaSubst
import           Refinery.Proof
import           Refinery.Telescope          (Telescope, (@>))
import qualified Refinery.Telescope          as Tl

newtype Tactic ext jdg m = Tactic { unTactic :: jdg -> m (ProofState ext jdg) }

type MultiTactic ext jdg m = Tactic ext (ProofState ext jdg) m

identity :: (MetaSubst ext ext m) => Tactic ext jdg m
identity = Tactic $ goal

compose :: (MetaSubst ext ext m, MetaSubst ext (MetaVar ext) m, MetaSubst ext jdg m) => Tactic ext jdg m -> MultiTactic ext jdg m -> Tactic ext jdg m
compose (Tactic t) (Tactic mt) = Tactic $ fmap flatten . mt <=< t

all :: (Monad m) => Tactic ext jdg m -> MultiTactic ext jdg m
all t = Tactic $ traverse (unTactic t)

instance (MetaSubst ext ext m, MetaSubst ext (MetaVar ext) m, MetaSubst ext jdg m) => Semigroup (Tactic ext jdg m) where
  t1 <> t2 = t1 `compose` (all t2)

instance (MetaSubst ext ext m, MetaSubst ext (MetaVar ext) m, MetaSubst ext jdg m) => Monoid (Tactic ext jdg m) where
  mempty = identity

each :: (MetaSubst ext ext m) => [Tactic ext jdg m] -> MultiTactic ext jdg m
each ts = Tactic $ fmap snd . mapAccumLM applyTac ts
  where
    applyTac (Tactic t:ts) j = (ts,) <$> t j
    applyTac [] j            = ([],) <$> (unTactic identity) j

(<..>) :: (MetaSubst ext ext m, MetaSubst ext (MetaVar ext) m, MetaSubst ext jdg m) => Tactic ext jdg m -> [Tactic ext jdg m] -> Tactic ext jdg m
t1 <..> ts = t1 `compose` (each ts)

orElse :: (MonadPlus m) => Tactic ext jdg m -> Tactic ext jdg m -> Tactic ext jdg m
orElse (Tactic t) (Tactic t') = Tactic $ \j -> (t j) `mplus` (t' j)

try :: (MetaSubst ext ext m, MonadPlus m) => Tactic ext jdg m -> Tactic ext jdg m
try t = t `orElse` identity

many :: (MetaSubst ext ext m, MetaSubst ext (MetaVar ext) m, MetaSubst ext jdg m, MonadPlus m) => Tactic ext jdg m -> Tactic ext jdg m
many t = try (t <> many t)


newtype TacticT ext jdg err m a = TacticT { unTacticT :: WriterT (Telescope ext jdg) (ExceptT err m) a }
  deriving
    ( Functor , Applicative, Monad
    , Alternative, MonadPlus
    , MonadError err, MonadWriter (Telescope ext jdg), MonadState s
    )

instance MonadTrans (TacticT ext jdg err) where
  lift = TacticT . lift . lift

runTacticT :: (Monad m) => TacticT ext jdg err m a -> m (Either err (a, Telescope ext jdg))
runTacticT = runExceptT . runWriterT . unTacticT

subgoal :: (MetaSubst ext ext m) => jdg -> TacticT ext jdg err m (MetaVar ext)
subgoal j = do
  x <- lift $ fresh
  tell (Tl.singleton x j)
  return x

tactic :: (Monad m) => (jdg -> TacticT ext jdg err m ext) -> Tactic ext jdg m
tactic t = Tactic $ \j -> runTacticT (t j) >>= \case
  Left err -> fail "Tactic Error!"
  Right (ext, goals) -> return $ ProofState goals ext

solve :: (Monad m) => Tactic ext jdg m -> jdg -> m (ProofState ext jdg)
solve (Tactic t) j = t j
