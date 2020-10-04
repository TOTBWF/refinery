{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Checkers where

import Control.Monad.State.Class
import Control.Monad.Error.Class
import Test.QuickCheck hiding (Failure)
import Test.QuickCheck.Checkers
import Control.Applicative

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

monadError
    :: forall m e a
     . ( MonadError e m
       , EqProp (m a)
       , Show (m a)
       , Show (a)
       , Show e
       , Function e
       , CoArbitrary e
       , Arbitrary e
       , Arbitrary a
       , Arbitrary (m a)
       )
    => m a
    -> TestBatch
monadError _ =
  ( "MonadError laws"
  , [ ("catchError (pure a) (const h)", property $ do
        a  <- arbitrary @a
        eh <- arbitrary @(m a)
        pure $
          counterexample (show a) $
          counterexample (show eh) $
            (catchError (pure a) (const eh)) =-= pure a
      )
    , ("catchError (throwError e) h", property $ do
        e <- arbitrary @e
        h <- arbitrary @(Fun e (m a))
        pure $
          counterexample (show e) $
          counterexample (show h) $
            (catchError (throwError e) (applyFun h)) =-= applyFun h e
      )
    , ("catchError (catchError a h1) h2", property $ do
        a <- arbitrary @(m a)
        h1 <- arbitrary @(Fun e (m a))
        h2 <- arbitrary @(Fun e (m a))
        pure $
          counterexample (show a) $
          counterexample (show h1) $
          counterexample (show h2) $
            catchError (catchError a (applyFun h1)) (applyFun h2) =-=
              (catchError a (\e -> catchError (applyFun h1 e) (applyFun h2)))
      )
    ]
  )


catchAlt
    :: forall m a e
     . ( MonadError e m
       , Alternative m
       , EqProp (m a)
       , Show e
       , Show (m a)
       , Function e
       , CoArbitrary e
       , Arbitrary e
       , Arbitrary (m a)
       )
    => m a
    -> Property
catchAlt _ = property $ do
  ma <- arbitrary @(m a)
  e <- arbitrary @e
  h <- arbitrary @(Fun e (m a))
  pure $
    counterexample (show ma) $
    counterexample (show e) $
    counterexample (show h) $
      catchError (ma <|> throwError e) (applyFun h) =-= applyFun h e

