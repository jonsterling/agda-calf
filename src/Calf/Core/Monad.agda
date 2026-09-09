module Calf.Core.Monad where

open import Cubical.Data.Sigma

open import Calf.Value

open import Calf.Core.Cost public

opaque
  M : 𝒱 → 𝒱
  M X = ℂ × X

  retᴹ : X → M X
  retᴹ x = 0ℂ , x
