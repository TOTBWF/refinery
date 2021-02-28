{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Except

import Refinery.ProofState
import Refinery.Tactic
import Data.List
import Data.String (IsString(..))

-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var String
  | Hole
  | Lam String Term
  | Pair Term Term
  deriving (Show)


-- The type part of simply typed lambda calculus
data Type
  = TVar String
  | Type :-> Type
  | TPair Type Type
  deriving (Show, Eq)

infixr 4 :->

instance IsString Type where
    fromString = TVar

-- A judgement is just a context, along with a goal
data Judgement = [(String, Type)] :- Type
  deriving (Show)

instance Semigroup Judgement where
    a <> _ = a
instance Monoid Judgement where
    mempty = [] :- TVar "uhh"

instance MonadExtract Term Identity where
    hole = pure Hole

type T a = TacticT Judgement Term String Int Identity a

pair :: T ()
pair = rule $ \case
    (hys :- TPair a b) -> Pair <$> subgoal (hys :- a) <*> subgoal (hys :- b)
    _                  -> unsolvable "goal mismatch: Pair"

lam :: T ()
lam = rule $ \case
    (hys :- (a :-> b)) -> do
        name <- gets show
        modify (+ 1)
        body <- subgoal $ ((name, a) : hys) :- b
        pure $ Lam name body
    _                  -> unsolvable "goal mismatch: Lam"

assumption :: T ()
assumption = rule $ \ (hys :- a) ->
  case find (\(_, ty) -> ty == a) hys of
    Just (x, _) -> pure $ Var x
    Nothing     -> unsolvable "goal mismatch: Assumption"

auto :: T ()
auto = do
    many_ lam
    choice [ pair >> auto
           , assumption
           ]

jdg :: Judgement
jdg = ([] :- ("a" :-> "b" :-> (TPair "a" "b")))

main :: IO ()
main = do
    print $ runTacticT auto jdg 0
