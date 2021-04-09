module Main where

import Test.Hspec

import Spec.PropertyTests
import Spec.STLC

main :: IO ()
main = hspec $ do
    propertyTests
    stlcTests
