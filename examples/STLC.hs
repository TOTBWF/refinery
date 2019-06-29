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
{-# LANGUAGE LambdaCase #-}
module STLC where

import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Trans
import Data.Functor.Identity

import Data.String (IsString)
import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Refinery.Tactic

newtype Var = V { unVar :: String }
  deriving (Show, Eq, Ord, IsString)

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
  deriving (Functor, Applicative, Monad, MonadError err, MonadRule jdg ext, MonadProvable jdg)

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

{- Tactics -}
type Tactic = TacticT Judgement Term (FreshT (ProvableT Judgement (Except TacticError))) ()

assumption :: Tactic
assumption = rule $ \(Judgement hy g) ->
  case find ((== g) . snd) hy of
    Just (n, _) -> return $ Var n
    Nothing -> throwError $ GoalMismatch "assumption" g

exact :: Var -> Tactic
exact x = rule $ \(Judgement hy g) ->
  case lookup x hy of
    Just t -> if t == g then return (Var x) else throwError (GoalMismatch "exact" g)
    Nothing -> throwError $ UndefinedHypothesis x

intro :: Var -> Tactic
intro x = rule $ \(Judgement hy g) ->
  case g of
    (TArrow a b) -> Lam x <$> subgoal (Judgement ((x, a):hy) b)
    _ -> throwError $ GoalMismatch "intro" g

intro_ :: Tactic
intro_ = rule $ \(Judgement hy g) ->
  case g of
    (TArrow a b) -> do
      x <- fresh "x"
      Lam x <$> subgoal (Judgement ((x, a):hy) b)
    _ -> throwError $ GoalMismatch "intro_" g

split :: Tactic
split = rule $ \(Judgement hy g) ->
  case g of
    (TPair l r) -> Pair <$> subgoal (Judgement hy l) <*> subgoal (Judgement hy r)
    _ -> throwError $ GoalMismatch "split" g

auto :: Tactic
auto = do
  intro_ <!> split <!> assumption
  auto

runTactic :: Type -> Tactic -> Either TacticError Term
runTactic ty tac = runExcept $ runProvableT $ runFreshT $ runTacticT tac (Judgement [] ty) >>= \case
  (t, []) -> return t
  (_, sg) -> throwError $ UnsolvedSubgoals sg

example1 = runTactic (TArrow (TVar "a") (TArrow (TVar "b") (TPair (TVar "b") (TArrow (TVar "c") (TVar "a"))))) $ do
  intro "x"
  intro "y"
  split <@>
    [ exact "y"
    , do
        intro "z"
        exact "x"
    ]
example2 = runTactic (TArrow (TVar "a") (TArrow (TVar "b") (TPair (TVar "b") (TArrow (TVar "c") (TVar "a"))))) auto
