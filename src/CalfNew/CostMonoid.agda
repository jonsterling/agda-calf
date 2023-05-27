{-# OPTIONS --cubical-compatible --safe #-}

module CalfNew.CostMonoid where

open import Agda.Builtin.Equality

record CostMonoid : Set₁ where
  infix 6 _⊕_

  field
    ℂ : Set
    _⊕_ : ℂ → ℂ → ℂ
    𝟘 : ℂ
    ⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
    ⊕-identityˡ : ∀ x → 𝟘 ⊕ x ≡ x
    ⊕-identityʳ : ∀ x → x ⊕ 𝟘 ≡ x

record ParCostMonoid : Set₁ where
  field
    costMonoid : CostMonoid

  open CostMonoid costMonoid public

  infixr 7 _⊗_

  field
    _⊗_ : ℂ → ℂ → ℂ
