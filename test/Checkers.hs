{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Checkers where

import Control.Monad.State.Class
import Test.QuickCheck hiding (Failure)
import Test.QuickCheck.Checkers

monadState
    :: forall m s a b
     . ( MonadState s m
       , EqProp (m s)
       , EqProp (m ())
       , Show s
       , Arbitrary s
       )
    => m (a, b)
    -> TestBatch
monadState _ =
  ( "MonadState laws"
  , [ ("get >> get", (get >> get) =-= get @s @m)
    , ("get >>= put", (get @s @m >>= put) =-= pure ())
    , ("put >> put", property $ do
        s1 <- arbitrary
        s2 <- arbitrary
        pure $
          counterexample (show s1) $
          counterexample (show s2) $
            (put @_ @m s1 >> put s2) =-= put s2
      )
    , ("put >> get", property $ do
        s <- arbitrary
        pure $
          counterexample (show s) $
            (put s >> get) =-= pure @m s
      )
    ]
  )

