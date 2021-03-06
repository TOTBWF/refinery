{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wredundant-constraints #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Spec.PropertyTests where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict (StateT (..))
import Control.Monad.State.Class
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
import Checkers
import Data.Foldable

testBatch :: TestBatch -> Spec
testBatch (batchName, tests) = describe ("laws for: " ++ batchName) $
  traverse_ (uncurry it) tests


instance (EqProp ext, EqProp meta, EqProp s, EqProp jdg) => EqProp (Proof s meta jdg ext) where

instance (MonadExtract meta ext err s m, EqProp (m (Either [err] [Proof s meta a ext])), Arbitrary s)
      => EqProp (ProofStateT ext ext err s m a) where
  (=-=) a b = property $ do
    s <- arbitrary
    pure $ ((=-=) `on` proofs s) a b

instance ( MonadExtract meta ext err s m
         , Arbitrary jdg
         , EqProp (m (Either [err] [Proof s meta jdg ext]))
         , Show s
         , Arbitrary s
         , Show jdg
         )
      => EqProp (TacticT jdg ext err s m a) where
  (=-=) = (=-=) `on` runTacticT . (() <$)

instance ( Arbitrary jdg
         , EqProp (m (Either [err] [Proof s meta jdg ext]))
         , MonadExtract meta ext err s m
         , Arbitrary s
         , Show s , Show jdg
         )
      => EqProp (RuleT jdg ext err s m ext) where
  (=-=) = (=-=) `on` rule . const

instance MonadExtract Int Int String Int Identity where
  hole = do
    i <- get
    modify (+1)
    pure (i, 0)
  unsolvableHole _ = do
    i <- get
    modify (+1)
    pure (i, 0)

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

decayArbitrary :: Arbitrary a => Int -> Gen a
decayArbitrary n = scale (`div` n) arbitrary

type ProofStateTest = ProofStateT Int Int String Int Identity
type RuleTest = RuleT Int Int String Int Identity
type TacticTest = TacticT (Sum Int) Int String Int Identity

propertyTests :: Spec
propertyTests = do
  describe "ProofStateT" $ do
    testBatch $ functor     (undefined :: ProofStateTest (Int, Int, Int))
    testBatch $ applicative (undefined :: ProofStateTest (Int, Int, Int))
    testBatch $ alternative (undefined :: ProofStateTest Int)
    testBatch $ monad       (undefined :: ProofStateTest (Int, Int, Int))
    testBatch $ monadPlus   (undefined :: ProofStateTest (Int, Int))
    testBatch $ monadState  (undefined :: ProofStateTest (Int, Int))
    it "distrib put over <|>" $ property $ distribPut (undefined :: ProofStateTest Int)
  describe "RuleT" $ do
    testBatch $ functor     (undefined :: RuleTest (Int, Int, Int))
    testBatch $ applicative (undefined :: RuleTest (Int, Int, Int))
    testBatch $ alternative (undefined :: RuleTest Int)
    testBatch $ monad       (undefined :: RuleTest (Int, Int, Int))
  describe "TacticT" $ do
    testBatch $ functor     (undefined :: TacticTest ((), (), ()))
    testBatch $ applicative (undefined :: TacticTest ((), (), ()))
    testBatch $ alternative (undefined :: TacticTest ())
    testBatch $ monad       (undefined :: TacticTest ((), (), ()))
    testBatch $ monadPlus   (undefined :: TacticTest ((), ()))
    testBatch $ monadState  (undefined :: TacticTest ((), ()))
    it "interleave - mzero" $ property $ interleaveMZero (undefined :: TacticTest Int)
    it "interleave - mplus" $ property $ interleaveMPlus (undefined :: TacticTest Int)
    it "distrib put over <|>" $ property $ distribPut (undefined :: TacticTest ())
    -- it "constant peek" $ property $ peekConst (undefined :: TacticTest ())

leftAltBind
    :: forall m a b
    . (EqProp (m b), Monad m, Alternative m)
    => m a -> m a -> (a -> m b)
    -> Property
leftAltBind m1 m2 f =
  ((m1 <|> m2) >>= f) =-= ((m1 >>= f) <|> (m2 >>= f))

rightAltBind
    :: forall m a
    . (EqProp (m a), Monad m, Alternative m)
    => m () -> m a -> m a
    -> Property
rightAltBind m1 m2 m3 =
  (m1 >> (m2 <|> m3)) =-= ((m1 >> m2) <|> (m1 >> m3))

interleaveMZero
    :: forall m a meta jdg ext err s
     . (MonadExtract meta ext err s m
       , EqProp (m (Either [err] [Proof s meta jdg ext]))
       , Show s , Show jdg
       , Arbitrary jdg, Arbitrary s)
    => TacticT jdg ext err s m a  -- ^ proxy
    -> TacticT jdg ext err s m a
    -> Property
interleaveMZero _ m =
    (mzero <%> m) =-= m

interleaveMPlus
    :: forall m a meta jdg ext err s
     . (MonadExtract meta ext err s m
       , EqProp (m (Either [err] [Proof s meta jdg ext]))
       , Show s , Show jdg
       , Arbitrary jdg, Arbitrary s)
    => TacticT jdg ext err s m a  -- ^ proxy
    -> a
    -> TacticT jdg ext err s m a
    -> TacticT jdg ext err s m a
    -> Property
interleaveMPlus _ a m1 m2 =
    ((pure a <|> m1) <%> m2) =-= (pure a <|> (m2 <%> m1))

distribPut
    :: forall s m a
     . ( MonadState s m
       , Alternative m
       , EqProp (m a)
       , Arbitrary (m a)
       , Arbitrary s
       , Show s
       , Show (m a)
       )
    => m a -> Property
distribPut _ = property $ do
  s <- arbitrary @s
  m1 <- arbitrary @(m a)
  m2 <- arbitrary @(m a)
  pure $
    counterexample (show s) $
    counterexample (show m1) $
    counterexample (show m2) $
      (put s >> (m1 <|> m2)) =-= ((put s >> m1) <|> (put s >> m2))

-- peekConst
--     :: forall m jdg ext err s
--      . (MonadExtract ext err m
--        , EqProp (m [Either err (Proof s jdg ext)])
--        , Show s , Show jdg
--        , Arbitrary jdg, Arbitrary s)
--     => TacticT jdg ext err s m ()  -- ^ proxy
--     -> TacticT jdg ext err s m ()
--     -> TacticT jdg ext err s m ()
--     -> Property
-- peekConst _ t t' =
--     peek t (const t') =-= (t' >> t)
