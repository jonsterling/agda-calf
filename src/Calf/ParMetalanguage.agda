{-# OPTIONS --prop --without-K --rewriting #-}

-- The basic CBPV metalanguage, extended with parallelism.

open import Calf.CostMonoid

module Calf.ParMetalanguage (ParCostMonoid : ParCostMonoid) where

open import Calf.Prelude
open ParCostMonoid ParCostMonoid
open import Calf.Metalanguage costMonoid public

postulate
  -- negative product
  _&_ : {A₁ A₂ : tp pos} → cmp (F A₁) → cmp (F A₂) → cmp (F (Σ++ A₁ (λ _ → A₂)))

  bind/par : ∀ {A₁ A₂} {X} {v₁ v₂ f p₁ p₂} → bind {Σ++ A₁ (λ _ → A₂)} X (step' (F A₁) p₁ (ret v₁) & step' (F A₂) p₂ (ret v₂)) f ≡ step' X (p₁ ⊗ p₂) (f (v₁ , v₂))
  {-# REWRITE bind/par #-}
  -- TODO: define tbind/par, dbind/par