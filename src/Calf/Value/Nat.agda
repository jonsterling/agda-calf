module Calf.Value.Nat where

open import Calf.Value

open import Cubical.Data.Nat public
  using (ℕ; zero; suc; _+_; isSetℕ)
open import Cubical.Data.Nat.Order public
  using (_≤_; isProp≤; ≤-refl; ≤-suc)

opaque
  unfolding 𝟚

  isDiscreteℕ : isDiscrete ℕ
  isDiscreteℕ = BEH⇒isDiscrete refl

ℕ₌ : 𝒱₌
ℕ₌ = ℕ , isSetℕ , isDiscreteℕ

ℕₚ : 𝒱ₚ
ℕₚ = ⟨ ℕ₌ ⟩ₚ
