{-# OPTIONS --rewriting #-}

module Calf.Data.Maybe where

open import Calf.Prelude
open import Calf.CBPV

open import Data.Maybe public renaming (maybe to maybe-case)

maybe : tp pos → tp pos
maybe A = meta⁺ (Maybe (val A))
