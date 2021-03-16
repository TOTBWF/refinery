{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Spec.STLC where

import Data.List
import Data.String (IsString(..))

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State

import Refinery.ProofState
import Refinery.Tactic

import Test.Hspec

-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var String
  | Hole
  | Lam String Term
  | Pair Term Term
  deriving (Show, Eq)


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
  deriving (Show, Eq)

instance MonadExtract Term String Identity where
    hole = pure Hole
    unsolvableHole _ = pure Hole

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

refine :: T ()
refine = do
    many_ lam
    try pair

testHandlers :: T ()
testHandlers = do
    handler (\err -> pure $ err ++ " Third")
    handler (\err -> pure $ err ++ " Second")
    failure "First"

testHandlerAlt :: T ()
testHandlerAlt = do
    handler (\err -> pure $ err ++ " Handled")
    (failure "Error1") <|> (failure "Error2")

jdg :: Judgement
jdg = ([] :- ("a" :-> "b" :-> (TPair "a" "b")))

stlcTests :: Spec
stlcTests = do
    describe "Simply Typed Lambda Calculus" $ do
        it "auto synthesize a solution" $ (runIdentity $ evalTacticT auto jdg 0) `shouldBe` [(Lam "0" $ Lam "1" $ Pair (Var "0") (Var "1"))]
        it "handler ordering is correct" $ (runIdentity $ runTacticT testHandlers jdg 0) `shouldBe` (Left ["First Second Third"])
        it "handler works through alt" $ (runIdentity $ runTacticT testHandlerAlt jdg 0) `shouldBe` (Left ["Error1 Handled","Error2 Handled"])
