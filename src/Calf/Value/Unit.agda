module Calf.Value.Unit where

open import Calf.Value

open import Cubical.Data.Unit public
  renaming (Unit to 1ᵛ; isSetUnit to isSet1ᵛ)

opaque
  isDiscrete1ᵛ : isDiscrete 1ᵛ
  isDiscrete1ᵛ = isLocalUnit

  isPreorder1ᵛ : isPreorder 1ᵛ
  isPreorder1ᵛ = isLocalUnit {F = Fᴾ}

1ᵛ₌ : 𝒱₌
1ᵛ₌ = 1ᵛ , isSet1ᵛ , isDiscrete1ᵛ
