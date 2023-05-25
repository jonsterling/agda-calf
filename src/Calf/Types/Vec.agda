{-# OPTIONS --cubical-compatible --prop --rewriting #-}

module Calf.Types.Vec where

open import Calf.Metalanguage
open import Calf.Types.Nat

open import Data.Vec.Base public using (Vec; []; _∷_)

vec : tp pos → val nat → tp pos
vec A n = U (meta (Vec (val A) n))
