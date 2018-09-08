module Addition where

import Refinery.Tactic

data Nat = Z | S Nat

data Judgement
    = Equals Nat Nat -- ^ x = y
    | Plus Nat Nat Nat -- ^ x = y + z


