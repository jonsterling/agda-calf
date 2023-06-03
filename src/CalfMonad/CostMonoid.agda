{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonoid where

open import Agda.Builtin.Equality

record CostMonoid {ℓ} (ℂ : Set ℓ) : Set ℓ where
  infix 5 _⊕_

  field
    _⊕_ : ℂ → ℂ → ℂ
    𝟘 : ℂ

    ⊕-assoc : ∀ p q r → (p ⊕ q) ⊕ r ≡ p ⊕ (q ⊕ r)
    ⊕-identityˡ : ∀ p → 𝟘 ⊕ p ≡ p
    ⊕-identityʳ : ∀ p → p ⊕ 𝟘 ≡ p

record ParCostMonoid {ℓ} (ℂ : Set ℓ) : Set ℓ where
  infix 5 _⊗_

  field
    _⊗_ : ℂ → ℂ → ℂ
