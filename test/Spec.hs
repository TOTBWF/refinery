{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# OPTIONS_GHC -Wredundant-constraints  #-}

module Main where

import Control.Monad.State.Strict (StateT (..))
import Data.Function
import Data.Functor.Identity
import Data.Monoid (Sum (..))
import Refinery.ProofState
import Refinery.Tactic
import Refinery.Tactic.Internal
import Test.Hspec
import Test.QuickCheck hiding (Failure)
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes

testBatch :: TestBatch -> Spec
testBatch (batchName, tests) = describe ("laws for: " ++ batchName) $
  foldr (>>) (return ()) (map (uncurry it) tests)


instance (MonadExtract ext m, EqProp (m [Either err (ext, [a])]))
      => EqProp (ProofStateT ext ext err m a) where
  (=-=) = (=-=) `on` proofs

instance (Show jdg, MonadExtract ext m, Arbitrary jdg, EqProp (m [Either err (ext, [jdg])]))
      => EqProp (TacticT jdg ext err m ()) where
  (=-=) = (=-=) `on` runTacticT

instance (Show jdg, Arbitrary jdg, EqProp (m [Either err (ext, [jdg])]), MonadExtract ext m)
      => EqProp (RuleT jdg ext err m ext) where
  (=-=) = (=-=) `on` rule . const

instance MonadExtract Int Identity where
  hole = pure 0

instance MonadProvable (Sum Int) Identity where
  proving = pure

instance (CoArbitrary ext', Arbitrary ext, Arbitrary err, Arbitrary a, Arbitrary (m (ProofStateT ext' ext err m a)))
      => Arbitrary (ProofStateT ext' ext err m a) where
  arbitrary = oneof
    [ Subgoal <$> decayArbitrary 2 <*> decayArbitrary 2
    , Effect  <$> arbitrary
    , Alt     <$> decayArbitrary 2 <*> decayArbitrary 2
    , pure Empty
    , Failure <$> arbitrary
    , Axiom   <$> arbitrary
    ]
  shrink = genericShrink

instance (Arbitrary (m (a, s)), CoArbitrary s) => Arbitrary (StateT s m a) where
  arbitrary = StateT <$> arbitrary

instance (CoArbitrary jdg, Arbitrary a, Arbitrary ext, Arbitrary err, CoArbitrary ext, Arbitrary jdg, Arbitrary (m (ProofStateT ext ext err m (a, jdg))))
      => Arbitrary (TacticT jdg ext err m a) where
  arbitrary = fmap (TacticT . StateT) arbitrary
  shrink = genericShrink

instance (Arbitrary a, Arbitrary err, CoArbitrary ext, Arbitrary jdg, Arbitrary (m (ProofStateT ext a err m jdg)))
      => Arbitrary (RuleT jdg ext err m a) where
  arbitrary = fmap RuleT arbitrary
  shrink = genericShrink

decayArbitrary :: Arbitrary a => Int -> Gen a
decayArbitrary n = scale (`div` n) arbitrary

main :: IO ()
main = hspec $ do
  describe "ProofStateT" $ do
    testBatch $ functor     $ (undefined :: ProofStateT Int Int String Identity (Int, Int, Int))
    testBatch $ applicative $ (undefined :: ProofStateT Int Int String Identity (Int, Int, Int))
    testBatch $ alternative $ (undefined :: ProofStateT Int Int String Identity Int)
    testBatch $ monad       $ (undefined :: ProofStateT Int Int String Identity (Int, Int, Int))
    testBatch $ monadPlus   $ (undefined :: ProofStateT Int Int String Identity (Int, Int))
  describe "RuleT" $ do
    testBatch $ functor     $ (undefined :: RuleT Int Int String Identity (Int, Int, Int))
    testBatch $ applicative $ (undefined :: RuleT Int Int String Identity (Int, Int, Int))
    testBatch $ monad       $ (undefined :: RuleT Int Int String Identity (Int, Int, Int))
  describe "TacticT" $ do
    testBatch $ functor     $ (undefined :: TacticT (Sum Int) Int String Identity ((), (), ()))
    testBatch $ applicative $ (undefined :: TacticT (Sum Int) Int String Identity ((), (), ()))
    testBatch $ alternative $ (undefined :: TacticT (Sum Int) Int String Identity ())
    testBatch $ monad       $ (undefined :: TacticT (Sum Int) Int String Identity ((), (), ()))
    testBatch $ monadPlus   $ (undefined :: TacticT (Sum Int) Int String Identity ((), ()))

