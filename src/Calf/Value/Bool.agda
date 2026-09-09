module Calf.Value.Bool where

open import Calf.Value
open import Calf.Value.Nat

open import Cubical.Data.Bool public

isDiscreteBool : isDiscrete Bool
isDiscreteBool = isLocalRetract inj prj isRetract isDiscreteℕ
  where
    inj : Bool → ℕ
    inj false = 0
    inj true = 1

    prj : ℕ → Bool
    prj zero = false
    prj (suc _) = true

    isRetract : retract inj prj
    isRetract false = refl
    isRetract true = refl

Bool₌ : 𝒱₌
Bool₌ = Bool , isSetBool , isDiscreteBool

Boolₚ : 𝒱ₚ
Boolₚ = ⟨ Bool₌ ⟩ₚ
