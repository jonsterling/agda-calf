{-# OPTIONS --prop --without-K --rewriting #-}

-- The basic CBPV metalanguage, extended with parallelism.

open import Calf.CostMonoid

module Calf.ParMetalanguage (parCostMonoid : ParCostMonoid) where

open ParCostMonoid parCostMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid

open import Calf.Eq
open import Calf.Bounded costMonoid

open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate
  -- negative product
  _&_ : {A₁ A₂ : tp pos} → cmp (F A₁) → cmp (F A₂) → cmp (F (Σ++ A₁ (λ _ → A₂)))

  &/join : ∀ {A₁ A₂} {v₁ v₂ p₁ p₂} →
    step (F A₁) p₁ (ret v₁) & step (F A₂) p₂ (ret v₂) ≡ step (F (Σ++ A₁ λ _ → A₂)) (p₁ ⊗ p₂) (ret (v₁ , v₂))
  {-# REWRITE &/join #-}

&/join/𝟘 : ∀ {A₁ A₂} {v₁ v₂} →
  ret v₁ & ret v₂ ≡ step (F (Σ++ A₁ λ _ → A₂)) (𝟘 ⊗ 𝟘) (ret (v₁ , v₂))
&/join/𝟘 = &/join {p₁ = 𝟘} {p₂ = 𝟘}
{-# REWRITE &/join/𝟘 #-}

bind/& : ∀ {A₁ A₂} {X} {v₁ v₂ f} (p₁ p₂ : ℂ) →
  bind {Σ++ A₁ λ _ → A₂} X (step (F A₁) p₁ (ret v₁) & step (F A₂) p₂ (ret v₂)) f ≡ step X (p₁ ⊗ p₂) (f (v₁ , v₂))
bind/& _ _ = refl

bound/par : {A₁ A₂ : tp pos} {e₁ : cmp (F A₁)} {e₂ : cmp (F A₂)} {c₁ c₂ : ℂ} →
  IsBounded A₁ e₁ c₁ →
  IsBounded A₂ e₂ c₂ →
  IsBounded (Σ++ A₁ λ _ → A₂) (e₁ & e₂) (c₁ ⊗ c₂)
bound/par (⇓ a₁ withCost p₁' [ h-bounded₁ , h-≡₁ ]) (⇓ a₂ withCost p₂' [ h-bounded₂ , h-≡₂ ]) with eq/ref h-≡₁ | eq/ref h-≡₂
... | refl | refl = ⇓ (a₁ , a₂) withCost (p₁' ⊗ p₂') [ (λ u → ⊗-mono-≤ (h-bounded₁ u) (h-bounded₂ u)) , (ret (eq/intro refl)) ]
