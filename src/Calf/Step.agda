{-# OPTIONS --prop --without-K --rewriting #-}

-- Step effect.

open import Calf.CostMonoid

module Calf.Step (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Relation.Binary.PropositionalEquality

cost : tp neg
cost = meta ℂ

postulate
  step : (X : tp neg) → cmp cost → cmp X → cmp X
  step/id : ∀ {X : tp neg} {e : cmp X} →
    step X zero e ≡ e
  {-# REWRITE step/id #-}
  step/concat : ∀ {X e p q} →
    step X p (step X q e) ≡ step X (p + q) e
  {-# REWRITE step/concat #-}

  U_step : ∀ {A} {X : val A → tp neg} {e n} → U (tbind {A} (step (F A) n e) X) ≡ U (tbind {A} e X)
  {-# REWRITE U_step #-}

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} {n} → step (Π A X) n f ≡ λ x → step (X x) n (f x)
  {-# REWRITE Π/step #-}

  bind/step : ∀ {A} {X} {e f n} → bind {A} X (step (F A) n e) f ≡ step X n (bind {A} X e f)
  dbind/step : ∀ {A} {X : val A → tp neg} {e f n} → dbind {A} X (step (F A) n e) f ≡ step (tbind {A} e X) n (dbind {A} X e f)
  {-# REWRITE bind/step dbind/step #-}

  step-mono-≲ : {X : tp neg} {c₁ c₂ : ℂ} {e₁ e₂ : cmp X} →
    ◯ (c₁ ≤ c₂) → _≲_ {X} e₁ e₂ → _≲_ {X} (step X c₁ e₁) (step X c₂ e₂)

  step/ext : ∀ X → (e : cmp X) → (c : ℂ) → ◯ (step X c e ≡ e)
  -- sadly the above cannot be made an Agda rewrite rule
