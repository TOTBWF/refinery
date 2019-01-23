{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
module STLC where

import Control.Monad.Except

import Refinery.Tactic

type Var = String

data Term
  = Var Var
  | Hole
  | Lam Var Term
  deriving (Show)

instance Extract Term where
  hole = Hole

data Type
  = TVar Var
  | TArrow Type Type
  deriving (Show, Eq)

data Judgement = Judgement [(Var, Type)] Type
  deriving (Show)

data TacticError
  = UndefinedHypothesis Var
  | GoalMismatch String Type
  | UnsolvedSubgoals [Judgement]
  deriving (Show)

exact :: (MonadError TacticError m) => Var -> TacticT Judgement Term m ()
exact s = rule $ \(Judgement hy g) ->
  case lookup s hy of
    Just t -> if t == g then return (Var s) else throwError (GoalMismatch "exact" t)
    Nothing -> throwError $ UndefinedHypothesis s

intro :: (MonadError TacticError m) => Var -> TacticT Judgement Term m ()
intro s = rule $ \(Judgement hy g) ->
  case g of
    (TArrow a b) -> Lam s <$> subgoal (Judgement ((s,a):hy) b)
    t -> throwError $ GoalMismatch "intro" t

runTactic :: Type -> TacticT Judgement Term (Except TacticError) () -> Either TacticError Term
runTactic ty tac = runExcept $ runTacticT tac (Judgement [] ty) >>= \case
  (t, []) -> return t
  (_, sg) -> throwError $ UnsolvedSubgoals sg

example = runTactic (TArrow (TVar "a") (TArrow (TVar "b") (TVar "a"))) $ do
  intro "x"
  intro "y"
  exact "x"
