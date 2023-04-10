{-# OPTIONS --prop --without-K --rewriting #-}

-- Probabilistic sampling.

open import Calf.CostMonoid

module Calf.Probability (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Relation.Binary.PropositionalEquality

open import Data.Interval

postulate
  flip : (X : tp neg) → 𝕀 → cmp X → cmp X → cmp X

  flip/0 : {X : tp neg} {e₀ e₁ : cmp X} →
    flip X 0𝕀 e₀ e₁ ≡ e₀
  flip/1 : {X : tp neg} {e₀ e₁ : cmp X} →
    flip X 1𝕀 e₀ e₁ ≡ e₁
  flip/same : {X : tp neg} {e : cmp X} {p : 𝕀} →
    flip X p e e ≡ e
  {-# REWRITE flip/0 flip/1 flip/same #-}

  flip/sym : {X : tp neg} {e₀ e₁ : cmp X} {p : 𝕀} →
    flip X p e₀ e₁ ≡ flip X (1- p) e₁ e₀
  flip/assocʳ : {X : tp neg} {e₀ e₁ e₂ : cmp X} {p q r : 𝕀} → p ≡ (p ∨ q) ∧ r →
    flip X p (flip X q e₀ e₁) e₂ ≡ flip X (p ∨ q) e₀ (flip X r e₁ e₂)

flip/assocˡ : {X : tp neg} {e₀ e₁ e₂ : cmp X} {p q r : 𝕀} → p ≡ (p ∧ q) ∨ r →
  flip X p e₀ (flip X q e₁ e₂) ≡ flip X (p ∧ q) (flip X r e₀ e₁) e₂
flip/assocˡ {X} {e₀} {e₁} {e₂} {p} {q} {r} h =
  let open ≡-Reasoning in
  begin
    flip X p e₀ (flip X q e₁ e₂)
  ≡⟨ cong (λ p → flip X p e₀ (flip X q e₁ e₂)) h ⟩
    flip X (p ∧ q ∨ r) e₀ (flip X q e₁ e₂)
  ≡˘⟨ flip/assocʳ {X} {e₀} {e₁} {e₂} (cong (_∧ q) h) ⟩
    flip X (p ∧ q) (flip X r e₀ e₁) e₂
  ∎

postulate
  -- bind/step : ∀ {A} {X} {e f n} → bind {A} X (step (F A) n e) f ≡ step X n (bind {A} X e f)
  flip/step : {X : tp neg} {c : cmp cost} {e₀ e₁ : cmp X} {p : 𝕀} →
    step X c (flip X p e₀ e₁) ≡ flip X p (step X c e₀) (step X c e₁)
{-# REWRITE flip/step #-}
