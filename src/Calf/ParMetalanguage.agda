{-# OPTIONS --prop --without-K --rewriting #-}

-- The basic CBPV metalanguage, extended with parallelism.

open import Calf.CostMonoid

module Calf.ParMetalanguage (parCostMonoid : ParCostMonoid) where

open ParCostMonoid parCostMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step ⊕-monoid
open import Data.Product

postulate
  -- negative product
  _&_ : {A₁ A₂ : tp pos} → cmp (F A₁) → cmp (F A₂) → cmp (F (Σ++ A₁ (λ _ → A₂)))

  &/par : ∀ {A₁ A₂} {v₁ v₂ p₁ p₂} →
    step' (F A₁) p₁ (ret v₁) & step' (F A₂) p₂ (ret v₂) ≡ step' (F (Σ++ A₁ λ _ → A₂)) (p₁ ⊗ p₂) (ret (v₁ , v₂))
  {-# REWRITE &/par #-}
