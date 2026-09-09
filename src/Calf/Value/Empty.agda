module Calf.Value.Empty where

open import Calf.Value

open import Cubical.Data.Empty public
  using ()
  renaming (⊥ to 0ᵛ; isProp⊥ to isProp0ᵛ)

isSet0ᵛ : isSet 0ᵛ
isSet0ᵛ = isProp→isSet isProp0ᵛ

opaque
  isDiscrete0ᵛ : isDiscrete 0ᵛ
  isDiscrete0ᵛ = isProp→isLocal (λ _ → 0𝟚) isProp0ᵛ

0ᵛ₌ : 𝒱₌
0ᵛ₌ = 0ᵛ , isSet0ᵛ , isDiscrete0ᵛ
