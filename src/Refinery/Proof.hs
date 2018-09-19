{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE GADTs        #-}
module Refinery.Proof
    (
      ProofState(..)
    , Provable
    , goal
    , flatten
    ) where

import           Prelude               hiding (concat)

import           Control.Applicative
import           Data.Functor.Identity

import           Refinery.MetaSubst
import           Refinery.Telescope    (Telescope (..), (@>))
import qualified Refinery.Telescope    as Tl

data ProofState ext jdg = ProofState (Telescope ext jdg) ext
  deriving (Functor, Foldable, Traversable)

class ( Eq (MetaVar ext)
      , Evidence ext
      , MetaSubst ext ext
      , MetaSubst ext (MetaVar ext)
      , MetaSubst ext jdg
      ) => Provable ext jdg

instance ( Eq (MetaVar ext)
         , Evidence ext
         , MetaSubst ext ext
         , MetaSubst ext (MetaVar ext)
         , MetaSubst ext jdg
         ) => Provable ext jdg

-- | Creates a proof state for a given judgement. Equivalent to monadic return.
goal :: (MonadName (MetaVar ext) m, Provable ext jdg) => jdg -> m (ProofState ext jdg)
goal j = fmap (\x -> ProofState (Tl.singleton x j) (hole x)) fresh


-- | Flattens out a series of nested proof states. Equivalent to monadic join.
flatten :: (Provable ext jdg) => ProofState ext (ProofState ext jdg) -> ProofState ext jdg
flatten (ProofState goals ext) =
  let (goals', _, ext') = Tl.foldlWithVar build (Tl.empty, [], ext) goals
  in (ProofState goals' ext')

  where
    build :: (Eq (MetaVar ext), MetaSubst ext ext, MetaSubst ext (MetaVar ext), MetaSubst ext jdg) =>
      (Telescope ext jdg, [(MetaVar ext, ext)], ext) ->
      MetaVar ext ->
      ProofState ext jdg ->
      (Telescope ext jdg, [(MetaVar ext, ext)], ext)
    build (tl, env, ext) x (ProofState tlx ax) =
      let tl' = tl <> metaSubsts env tlx
          env' = (x,ax):env
          ext' = metaSubst x ax ext
      in (tl', env', ext')
