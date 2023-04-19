{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

-- Upper bound on the cost of a computation.

module Calf.Types.Bounded (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Types.Eq
open import Calf.Step costMonoid

open import Calf.Types.Unit
open import Calf.Types.Bool
open import Calf.Types.Sum

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)


IsBounded : (A : tp pos) → cmp (F A) → ℂ → Set
IsBounded A e c =
  (result : cmp (F unit)) →
    _≲_ {F unit} (bind (F unit) e λ _ → result) (step (F unit) c result)

IsBounded⁻ : (A : tp pos) → cmp (F A) → ℂ → tp neg
IsBounded⁻ A e p = meta (IsBounded A e p)


bound/relax : ∀ {A e p p'} → ◯ (p ≤ p') → IsBounded A e p → IsBounded A e p'
bound/relax h ib result = ≲-trans (ib result) (step-mono-≲ {e₁ = result} h ≲-refl)

bound/circ : ∀ {A e} d {c} →
  IsBounded A e c →
  IsBounded A e (step (meta ℂ) d c)
bound/circ d {c} h result =
  ≲-trans (h result) (step-mono-≲ {e₁ = result} (λ u → Eq.subst (c ≤_) (Eq.sym (step/ext cost c d u)) ≤-refl) ≲-refl)

bound/ret : {A : tp pos} (a : val A) → IsBounded A (ret a) zero
bound/ret a result = ≲-refl

bound/step : {A : tp pos} (c' : ℂ) {c : ℂ} (e : cmp (F A)) →
  IsBounded A e c →
  IsBounded A (step (F A) c' e) (c' + c)
bound/step _ _ h result = step-mono-≲ (λ u → ≤-refl) (h result)

bound/bind/const : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (c d : ℂ) →
  IsBounded A e c →
  ((a : val A) → IsBounded B (f a) d) →
  IsBounded B (bind {A} (F B) e f) (c + d)
bound/bind/const {e = e} c d he hf result =
  ≲-trans
    (bind-mono-≲ {e₁ = e} ≲-refl λ a → hf a result)
    (bind-mono-≲ {f₁ = ret} (he (step (F unit) d result)) λ _ → ≲-refl)

bound/bool : ∀ {A : tp pos} {e0 e1} {p : val bool → cmp cost} →
  (b : val bool) →
  IsBounded A e0 (p false) →
  IsBounded A e1 (p true ) →
  IsBounded A (if b then e1 else e0) (p b)
bound/bool false h0 h1 = h0
bound/bool true  h0 h1 = h1

bound/sum/case/const/const : ∀ A B (C : val (sum A B) → tp pos) →
  (s : val (sum A B)) →
  (e0 : (a : val A) → cmp (F (C (inj₁ a)))) →
  (e1 : (b : val B) → cmp (F (C (inj₂ b)))) →
  (p : ℂ) →
  ((a : val A) → IsBounded (C (inj₁ a)) (e0 a) p) →
  ((b : val B) → IsBounded (C (inj₂ b)) (e1 b) p) →
  IsBounded (C s) (sum/case A B (λ s → F (C s)) s e0 e1) p
bound/sum/case/const/const A B C s e0 e1 p h1 h2 = sum/case A B
  (λ s → meta (IsBounded (C s) (sum/case A B (λ s₁ → F (C s₁)) s e0 e1) p)) s h1 h2
