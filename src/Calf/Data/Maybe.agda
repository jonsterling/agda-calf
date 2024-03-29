{-# OPTIONS --rewriting #-}

module Calf.Data.Maybe where

open import Calf.Prelude
open import Calf.CBPV

open import Data.Maybe public renaming (maybe to maybe-case)

maybe : tp⁺ → tp⁺
maybe A = meta⁺ (Maybe (val A))
