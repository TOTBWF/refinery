{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# OPTIONS_GHC -Wno-orphans            #-}
{-# LANGUAGE UndecidableInstances #-}

module Spec.STLC where

import Data.List
import Data.String (IsString(..))

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State.Strict

import Refinery.ProofState
import Refinery.Tactic

import GHC.Generics (Generic)
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck hiding (Failure)
import Refinery.Tactic.Internal
import Refinery.ProofState (pumpListT)


decayArbitrary :: Arbitrary a => Int -> Gen a
decayArbitrary n = scale (`div` n) arbitrary

instance ( CoArbitrary ext'
         , Arbitrary ext
         , CoArbitrary err
         , Arbitrary err
         , Arbitrary a
         , Arbitrary (m (ProofStateT ext' ext err s m a))
         , Arbitrary (m err)
         , CoArbitrary s
         , Arbitrary s
         )
      => Arbitrary (ProofStateT ext' ext err s m a) where
  arbitrary = getSize >>= \case
    n | n <= 1 -> oneof small
    _ -> oneof $
      [ Subgoal    <$> decayArbitrary 2 <*> decayArbitrary 2
      , Effect     <$> arbitrary
      , Interleave <$> decayArbitrary 2 <*> decayArbitrary 2
      , Alt        <$> decayArbitrary 2 <*> decayArbitrary 2
      , Stateful   <$> arbitrary
      , Failure    <$> arbitrary <*> decayArbitrary 2
      , Handle     <$> decayArbitrary 2 <*> arbitrary
      ] ++ small
    where
      small =
        [ pure Empty
        , Axiom   <$> arbitrary
        ]
  shrink = genericShrink

instance ( Arbitrary a
         , CoArbitrary err
         , Arbitrary err
         , CoArbitrary ext
         , Arbitrary jdg
         , Arbitrary (m (ProofStateT ext a err s m jdg))
         , Arbitrary (m err)
         , CoArbitrary s
         , Arbitrary s
         )
      => Arbitrary (RuleT jdg ext err s m a) where
  arbitrary = fmap RuleT arbitrary
  shrink = genericShrink

instance (Arbitrary (m (a, s)), CoArbitrary s) => Arbitrary (StateT s m a) where
  arbitrary = StateT <$> arbitrary

instance ( CoArbitrary jdg
         , Arbitrary a
         , Arbitrary ext
         , CoArbitrary err
         , Arbitrary err
         , CoArbitrary ext
         , Arbitrary jdg
         , Arbitrary (m (ProofStateT ext ext err s m (a, jdg)))
         , Arbitrary (m err)
         , CoArbitrary s
         , Arbitrary s
         )
      => Arbitrary (TacticT jdg ext err s m a) where
  arbitrary = fmap (TacticT . StateT) arbitrary
  shrink = genericShrink


-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var String
  | Hole Int
  | Lam String Term
  | Pair Term Term
  deriving (Show, Eq, Generic)

instance Arbitrary Term where
  arbitrary
    = let terminal = [Var <$> arbitrary, Hole <$> arbitrary]
      in
        sized
          $ (\ n
               -> case n <= 1 of
                    True -> oneof terminal
                    False
                      -> oneof
                           $ ([(Lam <$> arbitrary) <*> scale (subtract 1) arbitrary,
                               (Pair <$> scale (flip div 2) arbitrary)
                                 <*> scale (flip div 2) arbitrary]
                                <> terminal))




-- The type part of simply typed lambda calculus
data Type
  = TVar String
  | Type :-> Type
  | TPair Type Type
  deriving (Show, Eq, Generic)

instance CoArbitrary Type

instance Arbitrary Type where
  arbitrary
    = let terminal = [TVar <$> arbitrary]
      in
        sized
          $ (\ n
               -> case n <= 1 of
                    True -> oneof terminal
                    False
                      -> oneof
                           $ ([((:->) <$> scale (flip div 2) arbitrary)
                                 <*> scale (flip div 2) arbitrary,
                               (TPair <$> scale (flip div 2) arbitrary)
                                 <*> scale (flip div 2) arbitrary]
                                <> terminal))

data TacticState = TacticState { name :: Int, meta :: Int }
    deriving (Show, Eq)

instance Arbitrary TacticState where
  arbitrary = TacticState <$> arbitrary <*> arbitrary

instance CoArbitrary TacticState where
  coarbitrary (TacticState name meta) = coarbitrary (name, meta)

instance CoArbitrary Term where

instance CoArbitrary Judgement where


fresh :: MonadState TacticState m => m String
fresh = do
    nm <- gets (show . name)
    modify (\s -> s { name = name s + 1 })
    pure nm

infixr 4 :->

instance Semigroup Judgement where
  (<>) = error "it's not really a semigroup, dummy"

instance Monoid Judgement where
  mempty = [] :- TVar ""

instance IsString Type where
    fromString = TVar

-- A judgement is just a context, along with a goal
data Judgement = [(String, Type)] :- Type
  deriving (Show, Eq, Generic)

instance Arbitrary Judgement where
  arbitrary = (:-) <$> arbitrary <*> arbitrary

instance MonadExtract Int Term String TacticState Identity where
  hole = do
    m <- gets meta
    modify $ \ts -> ts { meta = m + 1}
    pure (m, Hole m)
  unsolvableHole _ = do
    m <- gets meta
    modify $ \ts -> ts { meta = m + 1}
    pure (m, Hole m)

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
    attempt lam (failure "Attempt Test Failed")
    failure $ "Attempt Test Succeeds"

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
        it "attempt properly handles errors" $ (evalT testAttempt jdg) `shouldBe` (Left ["Attempt Test Succeeds"])

    prop "yo" $ \(a :: T ()) b jdg st ->
      pumpListT (runStreamingTacticT (a <|> b) jdg st) ===
         mconcat
          [ pumpListT (runStreamingTacticT a jdg st)
          , pumpListT (runStreamingTacticT b jdg st)
          ]

    prop "yo" $ \(t :: T ()) (a :: T ()) jdg st ->
      pumpListT (runStreamingTacticT (rule subgoal >> a) jdg st) ===
        pumpListT (runStreamingTacticT a jdg st)
