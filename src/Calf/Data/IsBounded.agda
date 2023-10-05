{-# OPTIONS --rewriting #-}

open import Algebra.Cost

-- Upper bound on the cost of a computation.

module Calf.Data.IsBounded (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid

open import Calf.Data.IsBoundedG costMonoid public


IsBounded : (A : tp⁺) → cmp (F A) → ℂ → Set
IsBounded A e c = IsBoundedG A e (step⋆ c)


bound/relax : {c c' : ℂ} → c ≤ c' → {e : cmp (F A)} → IsBounded A e c → IsBounded A e c'
bound/relax h {e = e} = boundg/relax (step-monoˡ-≤⁻ (ret triv) h) {e = e}

bound/ret : {A : tp⁺} (a : val A) → IsBounded A (ret a) zero
bound/ret a = ≤⁻-refl

bound/step : {A : tp⁺} (c : ℂ) {c' : ℂ} (e : cmp (F A)) →
  IsBounded A e c' →
  IsBounded A (step (F A) c e) (c + c')
bound/step c {c'} e h = boundg/step c {b = step⋆ c'} e h

bound/bind/const : ∀ {A B : tp⁺} {e : cmp (F A)} {f : val A → cmp (F B)}
  (c d : ℂ) →
  IsBounded A e c →
  ((a : val A) → IsBounded B (f a) d) →
  IsBounded B (bind {A} (F B) e f) (c + d)
bound/bind/const {e = e} {f} c d he hf =
  let open ≤⁻-Reasoning cost in
  begin
    bind cost e (λ v → bind cost (f v) (λ _ → ret triv))
  ≤⟨ bind-monoʳ-≤⁻ e hf ⟩
    bind cost e (λ _ → step⋆ d)
  ≡⟨⟩
    bind cost (bind cost e λ _ → ret triv) (λ _ → step⋆ d)
  ≤⟨ bind-monoˡ-≤⁻ (λ _ → step⋆ d) he ⟩
    bind cost (step⋆ c) (λ _ → step⋆ d)
  ≡⟨⟩
    step⋆ (c + d)
  ∎


module Legacy where
  open import Calf.Data.Product
  open import Calf.Data.Equality

  legacy : {e : cmp (F A)} {c : ℂ} →
    val (Σ⁺ ℂ⁺ λ c' → meta⁺ (c' ≤ c) ×⁺ Σ⁺ A λ a → e ≡⁺[ U (F A) ] step (F A) c' (ret a)) →
    IsBounded A e c
  legacy {A} {e} {c} (c' , c'≤c , a , e≡step-ret) =
    let open ≤⁻-Reasoning cost in
    begin
      bind cost e (λ _ → ret triv)
    ≡⟨ cong (λ e → bind cost e (λ _ → ret triv)) e≡step-ret ⟩
      bind cost (step (F A) c' (ret a)) (λ _ → ret triv)
    ≡⟨⟩
      step⋆ c'
    ≤⟨ step-monoˡ-≤⁻ (ret triv) c'≤c ⟩
      step⋆ c
    ∎
