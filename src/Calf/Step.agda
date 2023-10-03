{-# OPTIONS --rewriting #-}

-- Step effect.

open import Algebra.Cost

module Calf.Step (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Phase.Core
open import Calf.Phase.Open
open import Relation.Binary.PropositionalEquality
open import Calf.Types.Product-

postulate
  step : (X : tp neg) → ℂ → cmp X → cmp X
  step/id : ∀ {X : tp neg} {e : cmp X} →
    step X zero e ≡ e
  {-# REWRITE step/id #-}
  step/concat : ∀ {X e p q} →
    step X p (step X q e) ≡ step X (p + q) e
  {-# REWRITE step/concat #-}

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} {n} → step (Π A X) n f ≡ λ x → step (X x) n (f x)
  {-# REWRITE Π/step #-}

  Σ⁻/step : ∀ {A P c e} → step (Σ⁻ A P) c e ≡ (proj₁ e , step (P (proj₁ e)) c (proj₂ e))
  {-# REWRITE Σ⁻/step #-}

  prod⁻/step : {X Y : tp neg} {c : ℂ} {e : cmp (prod⁻ X Y)} →
    step (prod⁻ X Y) c e ≡ (step X c (proj₁ e) , step Y c (proj₂ e))
  {-# REWRITE prod⁻/step  #-}

  open⁻/step : {X : ext → tp neg} {c : ℂ} {e : cmp (open⁻ X)} →
    step (open⁻ X) c e ≡ λ u → step (X u) c (e u)
  {-# REWRITE open⁻/step #-}

  bind/step : ∀ {A} {X} {e f n} → bind {A} X (step (F A) n e) f ≡ step X n (bind {A} X e f)
  {-# REWRITE bind/step #-}

  step/ext : ∀ X → (e : cmp X) → (c : ℂ) → ◯ (step X c e ≡ e)
  -- sadly the above cannot be made an Agda rewrite rule


postulate
  step-monoˡ-≲ : {X : tp neg} {c₁ c₂ : ℂ} (e : cmp X) →
    c₁ ≤ c₂ → _≲_ {X} (step X c₁ e) (step X c₂ e)

step-mono-≲ : {X : tp neg} {c₁ c₂ : ℂ} {e₁ e₂ : cmp X} →
  c₁ ≤ c₂ → _≲_ {X} e₁ e₂ → _≲_ {X} (step X c₁ e₁) (step X c₂ e₂)
step-mono-≲ {X} {c₂ = c₂} {e₁ = e₁} c₁≤c₂ e₁≲e₂ =
  ≲-trans (step-monoˡ-≲ e₁ c₁≤c₂) (≲-mono (step X c₂) e₁≲e₂)

step-monoʳ-≲ : {X : tp neg} (c : ℂ) {e₁ e₂ : cmp X} →
  _≲_ {X} e₁ e₂ → _≲_ {X} (step X c e₁) (step X c e₂)
step-monoʳ-≲ c e₁≲e₂ = step-mono-≲ (≤-refl {x = c}) e₁≲e₂
