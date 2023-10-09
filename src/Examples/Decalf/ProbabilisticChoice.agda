{-# OPTIONS --rewriting #-}

module Examples.Decalf.ProbabilisticChoice where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat
import Data.Nat.Properties as Nat
open import Calf.Data.List
open import Calf.Data.Equality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.IsBounded costMonoid
open import Function hiding (flip)

open import Data.Interval public


postulate
  flip : (X : tp⁻) → 𝕀 → cmp X → cmp X → cmp X

  flip/0 : {e₀ e₁ : cmp X} →
    flip X 0𝕀 e₀ e₁ ≡ e₀
  flip/1 : {e₀ e₁ : cmp X} →
    flip X 1𝕀 e₀ e₁ ≡ e₁
  flip/same : (X : tp⁻) (e : cmp X) {p : 𝕀} →
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

  flip/step : {e₀ e₁ : cmp X} {p : 𝕀} →
    step X c (flip X p e₀ e₁) ≡ flip X p (step X c e₀) (step X c e₁)


module _ where
  bernoulli : cmp cost
  bernoulli = flip cost ½ (step⋆ 0) (step⋆ 1)

  bernoulli/upper : bernoulli ≤⁻[ cost ] step⋆ 1
  bernoulli/upper =
    let open ≤⁻-Reasoning cost in
    begin
      flip cost ½ (step⋆ 0) (step⋆ 1)
    ≤⟨ ≤⁻-mono {cost} (λ e → flip cost ½ e (step⋆ 1)) (≤⁺-mono step⋆ (≤⇒≤⁺ (z≤n {1}))) ⟩
      flip cost ½ (step⋆ 1) (step⋆ 1)
    ≡⟨ flip/same cost (step⋆ 1) {½} ⟩
      step⋆ 1
    ∎

  binomial : cmp $ Π nat λ _ → cost
  binomial zero    = ret triv
  binomial (suc n) =
    bind cost bernoulli λ _ →
    binomial n

  binomial/comm : (n : val nat) →
    (bind cost bernoulli λ _ → binomial n) ≡ (bind cost (binomial n) λ _ → bernoulli)
  binomial/comm zero = refl
  binomial/comm (suc n) =
    let open ≡-Reasoning in
    begin
      ( bind cost bernoulli λ _ →
        bind cost bernoulli λ _ →
        binomial n
      )
    ≡⟨
      ( Eq.cong (bind cost bernoulli) $ funext λ _ →
        binomial/comm n
      )
    ⟩
      ( bind cost bernoulli λ _ →
        bind cost (binomial n) λ _ →
        bernoulli
      )
    ∎

  binomial/upper : (n : val nat) → binomial n ≤⁻[ cost ] step⋆ n
  binomial/upper zero    = ≤⁻-refl
  binomial/upper (suc n) =
    let open ≤⁻-Reasoning cost in
    begin
      ( bind cost bernoulli λ _ →
        binomial n
      )
    ≤⟨ ≤⁻-mono (λ e → bind cost e λ _ → binomial n) bernoulli/upper ⟩
      ( bind cost (step⋆ 1) λ _ →
        binomial n
      )
    ≡⟨⟩
      step cost 1 (binomial n)
    ≤⟨ ≤⁻-mono (step cost 1) (binomial/upper n) ⟩
      step⋆ (suc n)
    ∎


sublist : cmp $ Π (list A) λ _ → F (list A)
sublist {A} []       = ret []
sublist {A} (x ∷ xs) =
  bind (F (list A)) (sublist {A} xs) λ xs' →
  flip (F (list A)) ½ (ret xs') (step (F (list A)) 1 (ret (x ∷ xs')))

sublist/cost : cmp $ Π (list A) λ _ → cost
sublist/cost l = binomial (length l)

sublist/is-bounded : (l : val (list A)) → IsBoundedG (list A) (sublist {A} l) (sublist/cost {A} l)
sublist/is-bounded {A} []       = ≤⁻-refl
sublist/is-bounded {A} (x ∷ xs) =
    let open ≤⁻-Reasoning cost in
    begin
      bind cost
        ( bind (F (list A)) (sublist {A} xs) λ xs' →
          flip (F (list A)) ½ (ret xs') (step (F (list A)) 1 (ret (x ∷ xs')))
        )
        (λ _ → ret triv)
    ≡⟨⟩
      ( bind cost (sublist {A} xs) λ _ →
        flip cost ½ (ret triv) (step cost 1 (ret triv))
      )
    ≡⟨⟩
      ( bind cost (sublist {A} xs) λ _ →
        bernoulli
      )
    ≤⟨ ≤⁻-mono (λ e → bind cost e λ _ → bernoulli) (sublist/is-bounded {A} xs) ⟩
      ( bind cost (binomial (length xs)) λ _ →
        bernoulli
      )
    ≡˘⟨ binomial/comm (length xs) ⟩
      binomial (length (x ∷ xs))
    ∎

sublist/is-bounded' : (l : val (list A)) → IsBounded (list A) (sublist {A} l) (length l)
sublist/is-bounded' {A} l = ≤⁻-trans (sublist/is-bounded {A} l) (binomial/upper (length l))
