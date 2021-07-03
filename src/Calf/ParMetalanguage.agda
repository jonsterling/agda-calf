{-# OPTIONS --prop --without-K --rewriting #-}

-- The basic CBPV metalanguage, extended with parallelism.

open import Calf.CostMonoid

module Calf.ParMetalanguage (parCostMonoid : ParCostMonoid) where

open ParCostMonoid parCostMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Relation.Binary.PropositionalEquality
open import Calf.Step costMonoid
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Calf.Eq
open import Calf.Upper costMonoid

postulate
  -- negative product
  _&_ : {A₁ A₂ : tp pos} → cmp (F A₁) → cmp (F A₂) → cmp (F (Σ++ A₁ (λ _ → A₂)))

  &/par : ∀ {A₁ A₂} {v₁ v₂ p₁ p₂} →
    step (F A₁) p₁ (ret v₁) & step (F A₂) p₂ (ret v₂) ≡ step (F (Σ++ A₁ λ _ → A₂)) (p₁ ⊗ p₂) (ret (v₁ , v₂))
  {-# REWRITE &/par #-}

  bind/par/seq : {α : Set} {A₁ A₂ : tp pos} {κ : val (Σ++ A₁ (λ _ → A₂)) → α} {e₁ : cmp (F A₁)} {e₂ : cmp (F A₂)} →
    bind (meta α) (e₁ & e₂) κ ≡ bind (meta α) e₁ (λ v₁ → bind (meta α) e₂ (λ v₂ → κ (v₁ , v₂)))

&/par/𝟘 : ∀ {A₁ A₂} {v₁ v₂} → 
  ret v₁ & ret v₂ ≡ step (F (Σ++ A₁ λ _ → A₂)) (𝟘 ⊗ 𝟘) (ret (v₁ , v₂))
&/par/𝟘 = &/par {p₁ = 𝟘} {p₂ = 𝟘}
{-# REWRITE &/par/𝟘 #-}

bind/par : ∀ {A₁ A₂} {X} {v₁ v₂ f} (p₁ p₂ : ℂ) →
  bind {Σ++ A₁ λ _ → A₂} X (step (F A₁) p₁ (ret v₁) & step (F A₂) p₂ (ret v₂)) f ≡ step X (p₁ ⊗ p₂) (f (v₁ , v₂))
bind/par _ _ = refl

ub/par : {A₁ A₂ : tp pos} {e₁ : cmp (F A₁)} {e₂ : cmp (F A₂)} {p₁ p₂ : ℂ} →
  ub A₁ e₁ p₁ →
  ub A₂ e₂ p₂ →
  ub (Σ++ A₁ λ _ → A₂) (e₁ & e₂) (p₁ ⊗ p₂)
ub/par (ub/intro {p = p₁} {q = q₁} a₁ h≤₁ h≡₁) (ub/intro {p = p₂} {q = q₂} a₂ h≤₂ h≡₂) with eq/ref h≡₁ | eq/ref h≡₂
... | refl | refl = ub/intro (a₁ , a₂) (λ u → ⊗-mono-≤ (h≤₁ u) (h≤₂ u)) (ret (eq/intro refl))
