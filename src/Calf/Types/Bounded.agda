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
open import Calf.Types.BoundedG costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

IsBounded : (A : tp pos) → cmp (F A) → ℂ → Set
IsBounded A e c = IsBoundedG A e (step (F unit) c (ret triv))

IsBounded⁻ : (A : tp pos) → cmp (F A) → ℂ → tp neg
IsBounded⁻ A e p = meta (IsBounded A e p)


bound/relax : {c c' : ℂ} → c ≤ c' → ∀ {A e} → IsBounded A e c → IsBounded A e c'
bound/relax h {e = e} = boundg/relax (step-mono-≲ h (≲-refl {x = ret triv})) {e = e}

bound/ret : {A : tp pos} (a : val A) → IsBounded A (ret a) zero
bound/ret a result = ≲-refl

bound/step : {A : tp pos} (c : ℂ) {c' : ℂ} (e : cmp (F A)) →
  IsBounded A e c' →
  IsBounded A (step (F A) c e) (c + c')
bound/step c {c'} e h = boundg/step c {b = step (F unit) c' (ret triv)} e h

bound/bind/const : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (c d : ℂ) →
  IsBounded A e c →
  ((a : val A) → IsBounded B (f a) d) →
  IsBounded B (bind {A} (F B) e f) (c + d)
bound/bind/const {e = e} {f} c d he hf result =
  let open ≲-Reasoning (F unit) in
  begin
    bind (F unit) e (λ v → bind (F unit) (f v) (λ _ → result))
  ≤⟨ bind-mono-≲ {e₁ = e} ≲-refl (λ a → hf a result) ⟩
    bind (F unit) e (λ _ → step (F unit) d result)
  ≤⟨ bind-mono-≲ {f₁ = ret} (he (step (F unit) d result)) (λ _ → ≲-refl) ⟩
    step (F unit) (c + d) result
  ∎

bound/bool : ∀ {A : tp pos} {e0 e1} {p : val bool → ℂ} →
  (b : val bool) →
  IsBounded A e0 (p false) →
  IsBounded A e1 (p true ) →
  IsBounded A (if b then e1 else e0) (p b)
bound/bool {_} {e0} {e1} {p} = boundg/bool {_} {e0} {e1} {p = λ b → step (F unit) (p b) (ret triv)}

bound/sum/case/const/const : ∀ A B (C : val (sum A B) → tp pos) →
  (s : val (sum A B)) →
  (e0 : (a : val A) → cmp (F (C (inj₁ a)))) →
  (e1 : (b : val B) → cmp (F (C (inj₂ b)))) →
  (p : ℂ) →
  ((a : val A) → IsBounded (C (inj₁ a)) (e0 a) p) →
  ((b : val B) → IsBounded (C (inj₂ b)) (e1 b) p) →
  IsBounded (C s) (sum/case A B (λ s → F (C s)) s e0 e1) p
bound/sum/case/const/const A B C s e0 e1 p =
  boundg/sum/case/const/const A B C s e0 e1 (step (F unit) p (ret triv))
