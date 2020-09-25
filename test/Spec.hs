{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Main where

import Control.Monad
import Control.Monad.Logic.Class
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

instance ( Show jdg
         , MonadExtract ext m
         , Arbitrary jdg
         , EqProp (m [Either err (ext, [jdg])])
         )
      => EqProp (TacticT jdg ext err m a) where
  (=-=) = (=-=) `on` runTacticT . (() <$)

instance ( Show jdg
         , Arbitrary jdg
         , EqProp (m [Either err (ext, [jdg])])
         , MonadExtract ext m
         )
      => EqProp (RuleT jdg ext err m ext) where
  (=-=) = (=-=) `on` rule . const

instance MonadExtract Int Identity where
  hole = pure 0

instance MonadProvable (Sum Int) Identity where
  proving = pure

instance ( CoArbitrary ext'
         , Arbitrary ext
         , Arbitrary err
         , Arbitrary a
         , Arbitrary (m (ProofStateT ext' ext err m a))
         )
      => Arbitrary (ProofStateT ext' ext err m a) where
  arbitrary = getSize >>= \case
    n | n <= 1 -> oneof
      [ pure Empty
      , Failure <$> arbitrary
      , Axiom   <$> arbitrary
      ]
    _ -> oneof
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

instance ( CoArbitrary jdg
         , Arbitrary a
         , Arbitrary ext
         , Arbitrary err
         , CoArbitrary ext
         , Arbitrary jdg
         , Arbitrary (m (ProofStateT ext ext err m (a, jdg)))
         )
      => Arbitrary (TacticT jdg ext err m a) where
  arbitrary = fmap (TacticT . StateT) arbitrary
  shrink = genericShrink

instance ( Arbitrary a
         , Arbitrary err
         , CoArbitrary ext
         , Arbitrary jdg
         , Arbitrary (m (ProofStateT ext a err m jdg))
         )
      => Arbitrary (RuleT jdg ext err m a) where
  arbitrary = fmap RuleT arbitrary
  shrink = genericShrink

decayArbitrary :: Arbitrary a => Int -> Gen a
decayArbitrary n = scale (`div` n) arbitrary

type ProofStateTest = ProofStateT Int Int String Identity
type RuleTest = RuleT Int Int String Identity
type TacticTest = TacticT (Sum Int) Int String Identity

main :: IO ()
main = hspec $ do
  describe "ProofStateT" $ do
    testBatch $ functor     (undefined :: ProofStateTest (Int, Int, Int))
    testBatch $ applicative (undefined :: ProofStateTest (Int, Int, Int))
    testBatch $ alternative (undefined :: ProofStateTest Int)
    testBatch $ monad       (undefined :: ProofStateTest (Int, Int, Int))
    testBatch $ monadPlus   (undefined :: ProofStateTest (Int, Int))
    testBatch $ monadLogic  (undefined :: ProofStateTest (Int, Int))
  describe "RuleT" $ do
    testBatch $ functor     (undefined :: RuleTest (Int, Int, Int))
    testBatch $ applicative (undefined :: RuleTest (Int, Int, Int))
    testBatch $ monad       (undefined :: RuleTest (Int, Int, Int))
  describe "TacticT" $ do
    testBatch $ functor     (undefined :: TacticTest ((), (), ()))
    testBatch $ applicative (undefined :: TacticTest ((), (), ()))
    testBatch $ alternative (undefined :: TacticTest ())
    testBatch $ monad       (undefined :: TacticTest ((), (), ()))
    testBatch $ monadPlus   (undefined :: TacticTest ((), ()))
    testBatch $ monadLogic  (undefined :: TacticTest ((), ()))


monadLogic
    :: forall m a b
     . ( CoArbitrary a
       , Arbitrary (m b)
       , Arbitrary a
       , Arbitrary (m a)
       , MonadPlus m
       , MonadLogic m
       , EqProp (m b)
       , EqProp (m (Maybe (a, m a)))
       , Show a
       , Show (m a)
       , Show (m b)
       , Function a
       )
    => m (a, b)
    -> TestBatch
monadLogic _ =
  ( "MonadLogic laws"
  , [ ("msplit mzero", msplit @m @a mzero =-= return Nothing)
    , ("msplit mplus", property $ do
        a <- arbitrary
        m <- arbitrary
        pure $
          counterexample (show a) $
          counterexample (show m) $
            msplit @m @a (return a `mplus` m) =-= return (Just (a, m))
      )
    , ("ifte return", property $ do
        a <- arbitrary
        thf <- arbitrary
        let th = applyFun thf
        el <- arbitrary
        pure $
          counterexample (show a) $
          counterexample (show thf) $
          counterexample (show el) $
            ifte @m @a @b (return a) th el =-= th a
      )
    , ("ifte mzero", property $ do
        thf <- arbitrary
        let th = applyFun thf
        el <- arbitrary @(m b)
        pure $
          counterexample (show thf) $
          counterexample (show el) $
            ifte @m @a @b mzero th el =-= el
      )
    , ("ifte mplus", property $ do
        a <- arbitrary
        m <- arbitrary
        thf <- arbitrary
        let th = applyFun thf
        el <- arbitrary @(m b)
        pure $
          counterexample (show a) $
          counterexample (show m) $
          counterexample (show thf) $
          counterexample (show el) $
            ifte @m @a @b (return a `mplus` m) th el
              =-= th a `mplus` (m >>= th)
      )
    ]
  )

