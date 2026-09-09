module Calf.Value.Empty where

open import Calf.Value

open import Cubical.Data.Empty public
  hiding (rec)

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥

opaque
  isDiscrete⊥ : isDiscrete ⊥
  isDiscrete⊥ = isProp→isLocal (λ _ → 0𝟚) isProp⊥

⊥₌ : 𝒱₌
⊥₌ = ⊥ , isSet⊥ , isDiscrete⊥
