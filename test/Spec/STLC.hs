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
import Control.Monad.State

import Control.Monad.ST
import Data.STRef

import Refinery.ProofState
import Refinery.Tactic

import Test.Hspec
import Control.Monad.Reader

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

infixr 4 :->

instance IsString Type where
    fromString = TVar

-- A judgement is just a context, along with a goal
data Judgement = [(String, Type)] :- Type
  deriving (Show, Eq)

newtype FreshM s a = FreshM { runFreshM :: ReaderT (STRef s Int) (ST s) a }
    deriving (Functor, Applicative, Monad)

fresh :: FreshM s Int
fresh = FreshM $ do
  ref <- ask
  i <- lift $ readSTRef ref
  lift $ modifySTRef' ref (+ 1)
  pure i

instance MonadExtract Term String (FreshM s) where
    hole = Hole <$> fresh
    unsolvableHole _ = Hole <$> fresh

instance MonadNamedExtract Int Term (FreshM s) where
    namedHole = do
        i <- fresh
        return (i, Hole i)

instance MetaSubst Int Term where
    substMeta _ _ (Var s) = Var s
    substMeta i t1 (Hole i') = if i == i' then t1 else (Hole i')
    substMeta i t1 (Lam s body) = Lam s (substMeta i t1 body)
    substMeta i t1 (Pair l r) = Pair (substMeta i t1 l) (substMeta i t1 r)

type T s a = TacticT Judgement Term String Int (FreshM s) a

pair :: T s ()
pair = rule $ \case
    (hys :- TPair a b) -> Pair <$> subgoal (hys :- a) <*> subgoal (hys :- b)
    _                  -> unsolvable "goal mismatch: Pair"

lam :: T s ()
lam = rule $ \case
    (hys :- (a :-> b)) -> do
        name <- gets show
        modify (+ 1)
        body <- subgoal $ ((name, a) : hys) :- b
        pure $ Lam name body
    _                  -> unsolvable "goal mismatch: Lam"

assumption :: T s ()
assumption = rule $ \ (hys :- a) ->
  case find (\(_, ty) -> ty == a) hys of
    Just (x, _) -> pure $ Var x
    Nothing     -> unsolvable "goal mismatch: Assumption"

auto :: T s ()
auto = do
    many_ lam
    choice [ pair >> auto
           , assumption
           ]

refine :: T s ()
refine = do
    many_ lam
    try pair

testHandlers :: T s ()
testHandlers = do
    handler (\err -> pure $ err ++ " Third")
    handler (\err -> pure $ err ++ " Second")
    failure "First"

testHandlerAlt :: T s ()
testHandlerAlt = do
    handler (\err -> pure $ err ++ " Handled")
    (failure "Error1") <|> (failure "Error2")

testReify :: T s ()
testReify = do
    lam
    lam
    reify pair $ \ goals _ -> failure $ "Generated " <> show (length goals) <> " subgoals"

jdg :: Judgement
jdg = ([] :- ("a" :-> "b" :-> (TPair "a" "b")))

evalT :: (forall s. T s ()) -> Judgement -> Int -> Either [String] [Term]
evalT t j s = runST $ do
    ref <- newSTRef 0
    results <- flip runReaderT ref $ runFreshM $ runTacticT t j s
    pure $ fmap (fmap pf_extract) results

stlcTests :: Spec
stlcTests = do
    describe "Simply Typed Lambda Calculus" $ do
        it "auto synthesize a solution" $ (evalT auto jdg 0) `shouldBe` (Right [(Lam "0" $ Lam "1" $ Pair (Var "0") (Var "1"))])
        it "handler ordering is correct" $ (evalT testHandlers jdg 0) `shouldBe` (Left ["First Second Third"])
        it "handler works through alt" $ (evalT testHandlerAlt jdg 0) `shouldBe` (Left ["Error1 Handled","Error2 Handled"])
        it "reify gets the right subgoals" $ (evalT testReify jdg 0) `shouldBe` (Left ["Generated 2 subgoals"])
