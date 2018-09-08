{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-} {-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Refinery.Proof 
    (
      ProofState(..)
    , goal
    , flatten
    ) where

import Prelude hiding (concat)

import Data.Functor.Identity
import Control.Applicative
 

import Refinery.Telescope (Telescope(..), (@>))
import qualified Refinery.Telescope as Tl
import Refinery.MetaSubst

data ProofState ext jdg = ProofState (Telescope ext jdg) ext
  deriving (Functor, Foldable, Traversable)

-- | Creates a proof state for a given judgement. Equivalent to monadic return.
goal :: (MetaSubst ext ext m) => jdg -> m (ProofState ext jdg)
goal j = fmap (\x -> ProofState (Tl.singleton x j) (hole x)) fresh 

-- | Flattens out a series of nested proof states. Equivalent to monadic join.
flatten :: (MetaSubst ext ext m, MetaSubst ext (MetaVar ext) m, MetaSubst ext jdg m) => ProofState ext (ProofState ext jdg) -> ProofState ext jdg
flatten (ProofState goals ext) =
  let (goals', _, ext') = Tl.foldlWithVar (\(tl, env, ext) x (ProofState tlx ax) ->
                                                let tl' = tl <> metaSubsts env tlx
                                                    env' = (x,ax):env
                                                    ext' = metaSubst x ax ext
                                                in (tl', env', ext'))
                            (Tl.empty, [], ext) goals
  in (ProofState goals' ext')
