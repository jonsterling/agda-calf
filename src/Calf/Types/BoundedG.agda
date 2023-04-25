{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

-- Upper bound on the cost of a computation.

module Calf.Types.BoundedG (costMonoid : CostMonoid) where

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

IsBoundedG : (A : tp pos) → cmp (F A) → cmp (F unit) → Set
IsBoundedG A e b =
  (result : cmp (F unit)) →
    _≲_ {F unit} (bind (F unit) e λ _ → result) (bind (F unit) b λ _ → result)


boundg/relax : {b b' : cmp (F unit)}
  → _≲_ {F unit} b b'
  → {A : tp pos} {e : cmp (F A)}
  → IsBoundedG A e b
  → IsBoundedG A e b'
boundg/relax {b} {b'} h {e = e} ib-b result =
  let open ≲-Reasoning (F unit) in
  begin
    bind (F unit) e (λ _ → result)
  ≤⟨ ib-b result ⟩
    bind (F unit) b (λ _ → result)
  ≤⟨ bind-mono-≲ h (λ _ → ≲-refl {x = result}) ⟩
    bind (F unit) b' (λ _ → result)
  ∎

boundg/step : {A : tp pos} (c : ℂ) {b : cmp (F unit)} (e : cmp (F A)) →
  IsBoundedG A e b →
  IsBoundedG A (step (F A) c e) (step (F unit) c b)
boundg/step c _ h result = step-mono-≲ {c₁ = c} ≤-refl (h result)

boundg/bind : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (b : val A → cmp (F unit)) →
  ((a : val A) → IsBoundedG B (f a) (b a)) →
  IsBoundedG B (bind {A} (F B) e f) (bind {A} (F unit) e b)
boundg/bind {e = e} b hf result = bind-mono-≲ (≲-refl {x = e}) λ a → hf a result

boundg/bool : ∀ {A : tp pos} {e0 e1} {p : val bool → cmp (F unit)} →
  (b : val bool) →
  IsBoundedG A e0 (p false) →
  IsBoundedG A e1 (p true ) →
  IsBoundedG A (if b then e1 else e0) (p b)
boundg/bool false h0 h1 = h0
boundg/bool true  h0 h1 = h1

boundg/sum/case/const/const : ∀ A B (C : val (sum A B) → tp pos) →
  (s : val (sum A B)) →
  (e0 : (a : val A) → cmp (F (C (inj₁ a)))) →
  (e1 : (b : val B) → cmp (F (C (inj₂ b)))) →
  (p : cmp (F unit)) →
  ((a : val A) → IsBoundedG (C (inj₁ a)) (e0 a) p) →
  ((b : val B) → IsBoundedG (C (inj₂ b)) (e1 b) p) →
  IsBoundedG (C s) (sum/case A B (λ s → F (C s)) s e0 e1) p
boundg/sum/case/const/const A B C s e0 e1 p h1 h2 = sum/case A B
  (λ s → meta (IsBoundedG (C s) (sum/case A B (λ s₁ → F (C s₁)) s e0 e1) p)) s h1 h2
