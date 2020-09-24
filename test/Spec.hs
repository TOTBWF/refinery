{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Main where

import Control.Monad
import Control.Applicative
import Data.List
import Data.Function
import Data.Functor.Identity
import Test.Hspec
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Test.QuickCheck hiding (Failure)
import Refinery.ProofState

testBatch :: TestBatch -> Spec
testBatch (batchName, tests) = describe ("laws for: " ++ batchName) $
  foldr (>>) (return ()) (map (uncurry it) tests)


instance (Ord ext, Ord a, Monoid err, MonadExtract ext m, EqProp (m (Either err [(ext, [a])])))
      => EqProp (ProofStateT ext ext err m a) where
  -- (=-=) a b = (=-=) ((fmap . fmap) sort (proofs a)) ((fmap . fmap) sort (proofs b))
  (=-=) = (=-=) `on` proofs

instance MonadExtract Int Identity where
  hole = pure 0

-- deriving anyclass instance (Show ext', Arbitrary ext', EqProp err, EqProp ext, EqProp a, EqProp (m (ProofStateT ext' ext err m a)))
--   => EqProp (ProofStateT ext' ext err m a)

-- $>

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

decayArbitrary :: Arbitrary a => Int -> Gen a
decayArbitrary n = scale (`div` n) arbitrary

main :: IO ()
main = hspec $ do
  testBatch $ functor     $ (undefined :: ProofStateT Int Int String Identity (Int, Int, Int))
  testBatch $ applicative $ (undefined :: ProofStateT Int Int String Identity (Int, Int, Int))
  testBatch $ monad       $ (undefined :: ProofStateT Int Int String Identity (Int, Int, Int))
  testBatch $ monadPlus   $ (undefined :: ProofStateT Int Int String Identity (Int, Int))

