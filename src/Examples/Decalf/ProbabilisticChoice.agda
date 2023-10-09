{-# OPTIONS --rewriting #-}

module Examples.Decalf.ProbabilisticChoice where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Equality as Eq using (_≡_; module ≡-Reasoning)

open import Data.Interval public


postulate
  flip : (X : tp⁻) → 𝕀 → cmp X → cmp X → cmp X

  flip/0 : {e₀ e₁ : cmp X} →
    flip X 0𝕀 e₀ e₁ ≡ e₀
  flip/1 : {e₀ e₁ : cmp X} →
    flip X 1𝕀 e₀ e₁ ≡ e₁
  {-# REWRITE flip/0 flip/1 #-}
  flip/same : {e : cmp X} {p : 𝕀} →
    flip X p e e ≡ e

  flip/sym : (X : tp⁻) (p : 𝕀) (e₀ e₁ : cmp X) →
    flip X p e₀ e₁ ≡ flip X (1- p) e₁ e₀
  flip/assocʳ : (X : tp⁻) (e₀ e₁ e₂ : cmp X) {p q r : 𝕀} → p ≡ (p ∨ q) ∧ r →
    flip X p (flip X q e₀ e₁) e₂ ≡ flip X (p ∨ q) e₀ (flip X r e₁ e₂)

flip/assocˡ : (X : tp⁻) (e₀ e₁ e₂ : cmp X) {p q r : 𝕀} → p ≡ (p ∧ q) ∨ r →
  flip X p e₀ (flip X q e₁ e₂) ≡ flip X (p ∧ q) (flip X r e₀ e₁) e₂
flip/assocˡ X e₀ e₁ e₂ {p} {q} {r} h =
  let open ≡-Reasoning in
  begin
    flip X p e₀ (flip X q e₁ e₂)
  ≡⟨ Eq.cong (λ p → flip X p e₀ (flip X q e₁ e₂)) h ⟩
    flip X (p ∧ q ∨ r) e₀ (flip X q e₁ e₂)
  ≡˘⟨ flip/assocʳ X e₀ e₁ e₂ (Eq.cong (_∧ q) h) ⟩
    flip X (p ∧ q) (flip X r e₀ e₁) e₂
  ∎

postulate
  bind/flip : {f : val A → cmp X} {p : 𝕀} {e₀ e₁ : cmp (F A)} →
    bind {A = A} X (flip (F A) p e₀ e₁) f ≡ flip X p (bind X e₀ f) (bind X e₁ f)
  {-# REWRITE bind/flip #-}

  Π/flip : {X : val A → tp⁻} {p : 𝕀} {e₀ e₁ : cmp (Π A X)} →
    flip (Π A X) p e₀ e₁ ≡ λ a → flip (X a) p (e₀ a) (e₁ a)
  {-# REWRITE Π/flip #-}

  flip/step : {e₀ e₁ : cmp X} {p : 𝕀} →
    step X c (flip X p e₀ e₁) ≡ flip X p (step X c e₀) (step X c e₁)
  {-# REWRITE flip/step #-}
