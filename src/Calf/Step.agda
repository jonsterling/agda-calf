{-# OPTIONS --without-K #-}

-- Step effect.

open import Calf.CostMonoid

module Calf.Step (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Relation.Binary.PropositionalEquality
open import Calf.Types.Product

cost : tp neg
cost = meta ℂ

postulate
  step : ∀ (B : tp neg) → cmp cost → cmp B → cmp B
  step/id : ∀ {B : tp neg} {e : cmp B} →
    step B zero e ≡ e
  {-# REWRITE step/id #-}
  step/concat : ∀ {B e p q} →
    step B p (step B q e) ≡ step B (p + q) e
  {-# REWRITE step/concat #-}

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} {n} → step (Π A X) n f ≡ λ x → step (X x) n (f x)
  {-# REWRITE Π/step #-}

  Σ+-/step : ∀ {A P c e} → step (Σ+- A P) c e ≡ (proj₁ e , step (P (proj₁ e)) c (proj₂ e))
  {-# REWRITE Σ+-/step #-}

  prod⁻/step : {X Y : tp neg} {c : ℂ} {e : cmp (prod⁻ X Y)} →
    step (prod⁻ X Y) c e ≡ (step X c (proj₁ e) , step Y c (proj₂ e))
  {-# REWRITE prod⁻/step  #-}

  ext/cmp/step : {X : ext → tp neg} {c : ℂ} {e : cmp (ext/cmp X)} →
    step (ext/cmp X) c e ≡ λ u → step (X u) c (e u)
  {-# REWRITE ext/cmp/step #-}

  bind/step : ∀ {A} {X} {e f n} → bind {A} X (step (F A) n e) f ≡ step X n (bind {A} X e f)
  {-# REWRITE bind/step #-}

  step/ext : ∀ X → (e : cmp X) → (c : ℂ) → ◯ (step X c e ≡ e)
  -- sadly the above cannot be made an Agda rewrite rule

  extension/step : ∀ {X spec c e} →
    step [ X ∣ ext ↪ spec ] c e ≡
    record
      { out = step X c (out e)
      ; law = λ u → trans (step/ext X (out e) c u) (law e u)
      }
  {-# REWRITE extension/step #-}
