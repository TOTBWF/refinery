{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
module STLC where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.State.Strict
import Control.Monad.Trans
import Control.Applicative
import Data.Functor.Identity
import Data.Foldable

import Data.String (IsString)
import Data.List (find)
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Refinery.Tactic
import Refinery.SearchT

newtype Var = V { unVar :: String }
  deriving newtype (Show, Eq, Ord, IsString)

-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var Var
  | Hole Var
  | Lam Var Term
  | Pair Term Term
  deriving (Show)

-- The type part of simply typed lambda calculus
data Type
  = TVar Var
  | TArrow Type Type
  | TPair Type Type
  deriving (Show, Eq)

-- A judgement is just a context, along with a goal
data Judgement = Judgement [(Var, Type)] Type
  deriving (Show)

data TacticError
  = UndefinedHypothesis Var
  | GoalMismatch String Type
  | UnsolvedSubgoals [Judgement]
  deriving (Show)

{- Fresh variable generation -}
newtype FreshT m a = FreshT { unFreshT :: StateT (Map String Int) m a }
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadError err, MonadRule jdg ext, MonadProvable jdg)

runFreshT :: (Monad m) => FreshT m a -> m a
runFreshT (FreshT m) = evalStateT m (Map.empty)

class (Monad m) => MonadFresh m where
  fresh :: String -> m Var
  default fresh :: (MonadTrans t, MonadFresh m1, t m1 ~ m) => String -> m Var
  fresh = lift . fresh

instance (Monad m) => MonadFresh (FreshT m) where
  fresh n = FreshT $ gets (Map.lookup n) >>= \case
    Just i -> do
      modify (Map.adjust (+1) n)
      return $ V (n ++ show i)
    Nothing -> do
      modify (Map.insert n 1)
      return $ V n

instance (MonadFresh m) => MonadFresh (RuleT jdg ext m)

instance (MonadFresh m) => MonadExtract Term m where
  hole = Hole <$> fresh "_"

deriving anyclass instance (MonadFresh m) => MonadFresh (SearchT err m)
deriving anyclass instance (MonadProvable jdg m) => MonadProvable jdg (SearchT err m)

{- Tactics -}
type Tactic = TacticT Judgement Term (SearchT [TacticError] (FreshT (ProvableT Judgement IO))) ()

assumption :: Tactic
assumption = do
  (Judgement hy g) <- goal
  asumWith (throwError [GoalMismatch "assumption" g]) $ fmap (exact . fst) hy

exact :: Var -> Tactic
exact x = rule $ \(Judgement hy g) ->
  case lookup x hy of
    Just t -> if t == g then return (Var x) else throwError [GoalMismatch "exact" g]
    Nothing -> throwError $ [UndefinedHypothesis x]

intro :: Var -> Tactic
intro x = rule $ \(Judgement hy g) ->
  case g of
    (TArrow a b) -> Lam x <$> subgoal (Judgement ((x, a):hy) b)
    _ -> throwError $ [GoalMismatch "intro" g]

intro_ :: Tactic
intro_ = rule $ \(Judgement hy g) ->
  case g of
    (TArrow a b) -> do
      x <- fresh "x"
      Lam x <$> subgoal (Judgement ((x, a):hy) b)
    _ -> throwError $ [GoalMismatch "intro_" g]

split :: Tactic
split = rule $ \(Judgement hy g) ->
  case g of
    (TPair l r) -> Pair <$> subgoal (Judgement hy l) <*> subgoal (Judgement hy r)
    _ -> throwError $ [GoalMismatch "split" g]

auto :: Tactic
auto = do
  g <- goal
  liftIO $ print g
  -- try (intro_ >> auto)
  -- try (split >> auto)
  many_ intro_
  assumption
  -- intro_ <|> split <|> assumption

runTactic :: Type -> Tactic -> IO (Either [TacticError] (NonEmpty Term))
runTactic ty tac = runProvableT $ runFreshT $ observeAllT $ runTacticT tac (Judgement [] ty) >>= \case
  (t, []) -> return t
  (_, sg) -> throwError $ [UnsolvedSubgoals sg]

example1 = runTactic (TArrow (TVar "a") (TArrow (TVar "b") (TPair (TVar "b") (TArrow (TVar "c") (TVar "a"))))) $ do
  intro "x"
  intro "y"
  split <@>
    [ exact "y"
    , do
        intro "z"
        exact "x"
    ]
-- a -> b -> (b, c -> a)
example2 = runTactic (TArrow (TVar "a") (TArrow (TVar "b") (TPair (TVar "b") (TArrow (TVar "c") (TVar "a"))))) auto

example3 = runTactic (TArrow (TVar "a") (TArrow (TVar "a") (TVar "a"))) $ do
  many_ intro_
  assumption
  -- intro "x"
  -- intro "y"
  -- exact "x" <|> exact "y"
  --