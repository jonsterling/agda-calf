{-# OPTIONS --prop --without-K --rewriting #-}

-- Probabilistic sampling.

open import Calf.CostMonoid

module Calf.Probability (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Relation.Binary.PropositionalEquality

open import Data.Interval public

postulate
  flip : (X : tp neg) → 𝕀 → cmp X → cmp X → cmp X

  flip/0 : {X : tp neg} {e₀ e₁ : cmp X} →
    flip X 0𝕀 e₀ e₁ ≡ e₀
  flip/1 : {X : tp neg} {e₀ e₁ : cmp X} →
    flip X 1𝕀 e₀ e₁ ≡ e₁
  flip/same : {X : tp neg} {e : cmp X} {p : 𝕀} →
    flip X p e e ≡ e
  {-# REWRITE flip/0 flip/1 flip/same #-}

  flip/sym : (X : tp neg) (p : 𝕀) (e₀ e₁ : cmp X) →
    flip X p e₀ e₁ ≡ flip X (1- p) e₁ e₀
  flip/assocʳ : (X : tp neg) (e₀ e₁ e₂ : cmp X) {p q r : 𝕀} → p ≡ (p ∨ q) ∧ r →
    flip X p (flip X q e₀ e₁) e₂ ≡ flip X (p ∨ q) e₀ (flip X r e₁ e₂)

flip/assocˡ : (X : tp neg) (e₀ e₁ e₂ : cmp X) {p q r : 𝕀} → p ≡ (p ∧ q) ∨ r →
  flip X p e₀ (flip X q e₁ e₂) ≡ flip X (p ∧ q) (flip X r e₀ e₁) e₂
flip/assocˡ X e₀ e₁ e₂ {p} {q} {r} h =
  let open ≡-Reasoning in
  begin
    flip X p e₀ (flip X q e₁ e₂)
  ≡⟨ cong (λ p → flip X p e₀ (flip X q e₁ e₂)) h ⟩
    flip X (p ∧ q ∨ r) e₀ (flip X q e₁ e₂)
  ≡˘⟨ flip/assocʳ X e₀ e₁ e₂ (cong (_∧ q) h) ⟩
    flip X (p ∧ q) (flip X r e₀ e₁) e₂
  ∎

postulate
  bind/flip : {A : tp pos} {X : tp neg} {f : val A → cmp X} {p : 𝕀} {e₀ e₁ : cmp (F A)} →
    bind {A = A} X (flip (F A) p e₀ e₁) f ≡ flip X p (bind X e₀ f) (bind X e₁ f)
  {-# REWRITE bind/flip #-}

  Π/flip : {A : tp pos} {X : val A → tp neg} {p : 𝕀} {e₀ e₁ : cmp (Π A X)} →
    flip (Π A X) p e₀ e₁ ≡ λ a → flip (X a) p (e₀ a) (e₁ a)
  {-# REWRITE Π/flip #-}

  flip/step : {X : tp neg} {c : cmp cost} {e₀ e₁ : cmp X} {p : 𝕀} →
    step X c (flip X p e₀ e₁) ≡ flip X p (step X c e₀) (step X c e₁)
{-# REWRITE flip/step #-}
