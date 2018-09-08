{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module Refinery.Extract
    ( extract
    ) where

import Control.Monad.Writer

import Data.Maybe (catMaybes)

import Data.Typeable

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.TH

import Refinery.MetaSubst
import Refinery.Telescope (Telescope(..))
import qualified Refinery.Telescope as Tl
import Refinery.Proof


extract :: (MetaSubst ext ext m) => ProofState ext jdg -> ([jdg], Maybe ext)
extract = \case
  (Unsolved j) -> ([j], Nothing)
  (Subgoals goals ext) ->
    let (js, xs) = foldr collectErrors ([],[]) $ Tl.toList $ extract <$> goals
    in (js, Just $ metaSubsts xs ext)
  where
    collectErrors :: (MetaVar ext, ([jdg], Maybe ext)) -> ([jdg], [(MetaVar ext, ext)]) -> ([jdg], [(MetaVar ext, ext)])
    collectErrors (_, (j, Nothing)) (js, exts) = (j ++ js, exts)
    collectErrors (x, (j, Just e)) (js, exts) = (j ++ js, (x,e):exts)
