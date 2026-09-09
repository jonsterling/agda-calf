module Calf.Value.Sum where

open import Calf.Value
open import Calf.Value.Bool
open import Calf.Value.Sigma

open import Cubical.Data.Sum public
  renaming (inl to inj₁; inr to inj₂)

open Iso

⊎-Iso-Σ : Iso (X ⊎ Y) (Σ Bool (if_then Y else X))
⊎-Iso-Σ .fun (inj₁ x) = false , x
⊎-Iso-Σ .fun (inj₂ y) = true , y
⊎-Iso-Σ .inv (false , x) = inj₁ x
⊎-Iso-Σ .inv (true , y) = inj₂ y
⊎-Iso-Σ .rightInv (false , x) = refl
⊎-Iso-Σ .rightInv (true , y) = refl
⊎-Iso-Σ .leftInv (inj₁ x) = refl
⊎-Iso-Σ .leftInv (inj₂ y) = refl

opaque
  isPreorder⊎ : isPreorder X → isPreorder Y → isPreorder (X ⊎ Y)
  isPreorder⊎ {X} {Y} isPreorderX isPreorderY =
    isLocalRetract (⊎-Iso-Σ .fun) (⊎-Iso-Σ .inv) (⊎-Iso-Σ .leftInv)
      (isPreorderΣ Bool₌ λ { false → isPreorderX ; true → isPreorderY })

opaque
  isDiscrete⊎ : isDiscrete X → isDiscrete Y → isDiscrete (X ⊎ Y)
  isDiscrete⊎ isDiscreteX isDiscreteY =
    isLocalRetract (⊎-Iso-Σ .fun) (⊎-Iso-Σ .inv) (⊎-Iso-Σ .leftInv)
      (isDiscreteΣ isDiscreteBool λ { false → isDiscreteX ; true → isDiscreteY })

infixr 4 _⊎₌_

_⊎₌_ : 𝒱₌ → 𝒱₌ → 𝒱₌
X ⊎₌ Y =
  (⟨ X ⟩ ⊎ ⟨ Y ⟩) ,
  isSet⊎ (str X .fst) (str Y .fst) ,
  isDiscrete⊎ (str X .snd) (str Y .snd)
