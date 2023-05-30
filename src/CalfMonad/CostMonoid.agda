{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonoid ℓ where

open Agda.Primitive
open import Agda.Builtin.Equality

record CostMonoid : Set (lsuc ℓ) where
  infixr 5 _⊕_

  field
    ℂ : Set ℓ
    _⊕_ : ℂ → ℂ → ℂ
    𝟘 : ℂ
    ⊕-assoc : ∀ p q r → (p ⊕ q) ⊕ r ≡ p ⊕ (q ⊕ r)
    ⊕-identityˡ : ∀ p → 𝟘 ⊕ p ≡ p
    ⊕-identityʳ : ∀ p → p ⊕ 𝟘 ≡ p

record ParCostMonoid : Set (lsuc ℓ) where
  infixr 6 _⊗_

  field
    costMonoid : CostMonoid

  open CostMonoid costMonoid public

  field
    _⊗_ : ℂ → ℂ → ℂ
