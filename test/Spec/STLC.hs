{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
  | Hole Int
  | Lam String Term
  | Pair Term Term
  deriving (Show, Eq)


-- The type part of simply typed lambda calculus
data Type
  = TVar String
  | Type :-> Type
  | TPair Type Type
  deriving (Show, Eq)

data TacticState = TacticState { name :: Int, meta :: Int }
    deriving Show

fresh :: MonadState TacticState m => m String
fresh = do
    nm <- gets (show . name)
    modify (\s -> s { name = name s + 1 })
    pure nm

infixr 4 :->

instance IsString Type where
    fromString = TVar

-- A judgement is just a context, along with a goal
data Judgement = [(String, Type)] :- Type
  deriving (Show, Eq)

instance MonadExtract Int Term String TacticState Identity where
    hole s =
        let m = meta s
        in pure (m, Hole m, s { meta = 1 + m })
    unsolvableHole s _ =
        let m = meta s
        in pure (m, Hole m, s { meta = 1 + m })

instance MetaSubst Int Term where
    substMeta _ _ (Var s) = Var s
    substMeta i t1 (Hole i') = if i == i' then t1 else (Hole i')
    substMeta i t1 (Lam s body) = Lam s (substMeta i t1 body)
    substMeta i t1 (Pair l r) = Pair (substMeta i t1 l) (substMeta i t1 r)

type T a = TacticT Judgement Term String TacticState Identity a

pair :: T ()
pair = rule $ \case
    (hys :- TPair a b) -> Pair <$> subgoal (hys :- a) <*> subgoal (hys :- b)
    _                  -> unsolvable "goal mismatch: Pair"

lam :: T ()
lam = rule $ \case
    (hys :- (a :-> b)) -> do
        nm <- fresh
        body <- subgoal $ ((nm, a) : hys) :- b
        pure $ Lam nm body
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

testReify :: T ()
testReify = do
    lam
    lam
    reify pair $ \ (Proof _ _ goals) -> failure $ "Generated " <> show (length goals) <> " subgoals"

testAttempt :: T ()
testAttempt = do
    lam
    attempt pair lam
    _ :- g <- goal
    failure $ show g

jdg :: Judgement
jdg = ([] :- ("a" :-> "b" :-> (TPair "a" "b")))

evalT :: T () -> Judgement -> Either [String] [Term]
evalT t j = fmap (fmap pf_extract) $ runIdentity $ runTacticT t j (TacticState 0 0)

stlcTests :: Spec
stlcTests = do
    describe "Simply Typed Lambda Calculus" $ do
        it "auto synthesize a solution" $ (evalT auto jdg) `shouldBe` (Right [(Lam "0" $ Lam "1" $ Pair (Var "0") (Var "1"))])
        it "handler ordering is correct" $ (evalT testHandlers jdg) `shouldBe` (Left ["First Second Third"])
        it "handler works through alt" $ (evalT testHandlerAlt jdg) `shouldBe` (Left ["Error1 Handled","Error2 Handled"])
        it "reify gets the right subgoals" $ (evalT testReify jdg) `shouldBe` (Left ["Generated 2 subgoals"])
        it "attempt properly handles errors" $ (evalT testAttempt jdg) `shouldBe` (Left ["TPair (TVar \"a\") (TVar \"b\")"])
