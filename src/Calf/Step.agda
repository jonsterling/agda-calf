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
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality


variable
  c c' c₁ c₂ : ℂ

ℂ⁺ : tp pos
ℂ⁺ = meta⁺ ℂ


postulate
  step : (X : tp neg) → ℂ → cmp X → cmp X

  step/0 : {e : cmp X} →
    step X zero e ≡ e
  step/+ : {e : cmp X} →
    step X c₁ (step X c₂ e) ≡ step X (c₁ + c₂) e
  {-# REWRITE step/0 step/+ #-}

  step/ext : (X : tp neg) (e : cmp X) (c : ℂ) (u : ext) → step X c e ≡ e
  -- sadly the above cannot be made an Agda rewrite rule


postulate
  bind/step : {e : cmp (F A)} {f : val A → cmp X} →
    bind X (step (F A) c e) f ≡ step X c (bind X e f)
  {-# REWRITE bind/step #-}

  Π/step : {X : val A → tp neg} {f : cmp (Π A X)} →
    step (Π A X) c f ≡ λ a → step (X a) c (f a)
  {-# REWRITE Π/step #-}

  prod⁻/step : {e : cmp (prod⁻ X Y)} →
    step (prod⁻ X Y) c e ≡ (step X c (proj₁ e) , step Y c (proj₂ e))
  {-# REWRITE prod⁻/step  #-}

  unit⁻/step : {e : cmp unit⁻} →
    step unit⁻ c e ≡ triv
  {-# REWRITE unit⁻/step  #-}

  Σ⁻/step : {X : val A → tp neg} {e : cmp (Σ⁻ A X)} →
    step (Σ⁻ A X) c e ≡ (proj₁ e , step (X (proj₁ e)) c (proj₂ e))
  {-# REWRITE Σ⁻/step #-}

  open⁻/step : {X : ext → tp neg} {e : cmp (open⁻ X)} →
    step (open⁻ X) c e ≡ λ u → step (X u) c (e u)
  {-# REWRITE open⁻/step #-}


postulate
  ≤⇒≤⁺ : _≤_ ⇒ _≤⁺_ {ℂ⁺}

step-monoˡ-≤⁻ : (e : cmp X) →
  c ≤ c' → step X c e ≤⁻[ X ] step X c' e
step-monoˡ-≤⁻ {X} e c≤c' = ≤⁺-mono (λ c → step X c e) (≤⇒≤⁺ c≤c')

step-monoʳ-≤⁻ : (c : ℂ) {e e' : cmp X} →
  _≤⁻_ {X} e e' → _≤⁻_ {X} (step X c e) (step X c e')
step-monoʳ-≤⁻ {X} c = ≤⁻-mono (step X c)

step-mono-≤⁻ : {e e' : cmp X} →
  c ≤ c' → e ≤⁻[ X ] e' → step X c e ≤⁻[ X ] step X c' e'
step-mono-≤⁻ {X} {c} {c'} {e} {e'} c≤c' e≤e' =
  let open ≤⁻-Reasoning X in
  begin
    step X c e
  ≤⟨ step-monoˡ-≤⁻ e c≤c' ⟩
    step X c' e
  ≤⟨ step-monoʳ-≤⁻ c' e≤e' ⟩
    step X c' e'
  ∎
