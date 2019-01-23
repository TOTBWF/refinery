{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
module STLC where

import Control.Monad.Except
import Control.Monad.State

import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Refinery.Tactic

type Var = String

-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var Var
  | Hole
  | Lam Var Term
  | Pair Term Term
  deriving (Show)

instance Extract Term where
  hole = Hole

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

-- We need to keep track of the bound variables for fresh name generation

type Tactic = TacticT Judgement Term (StateT (Map String Int) (Except TacticError)) ()

fresh :: (MonadState (Map String Int) m) => String -> m Var
fresh n = gets (Map.lookup n) >>= \case
  Just i -> do
    modify (Map.adjust (+1) n)
    return (n ++ show i)
  Nothing -> do
    modify (Map.insert n 1)
    return n

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
runTactic ty tac = runExcept $ flip evalStateT Map.empty $ runTacticT tac (Judgement [] ty) >>= \case
  (t, []) -> return t
  (_, sg) -> throwError $ UnsolvedSubgoals sg

-- a -> b -> (b, c -> a)
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
