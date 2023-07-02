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

cost : tp neg
cost = F unit

-- (e ; ret triv) ≲ b
IsBoundedG : (A : tp pos) → cmp (F A) → cmp cost → Set
IsBoundedG A e b = _≲_ {cost} (bind cost e λ _ → ret triv) b

step⋆ : ℂ → cmp cost
step⋆ c = step cost c (ret triv)

step⋆-mono-≲ : {c₁ c₂ : ℂ} → c₁ ≤ c₂ → _≲_ {cost} (step⋆ c₁) (step⋆ c₂)
step⋆-mono-≲ c₁≤c₂ = step-monoˡ-≲ (ret triv) c₁≤c₂


boundg/relax : {b b' : cmp cost}
  → _≲_ {cost} b b'
  → {A : tp pos} {e : cmp (F A)}
  → IsBoundedG A e b
  → IsBoundedG A e b'
boundg/relax {b} {b'} h {e = e} ib-b =
  let open ≲-Reasoning cost in
  begin
    bind cost e (λ _ → ret triv)
  ≤⟨ ib-b ⟩
    b
  ≤⟨ h ⟩
    b'
  ∎

boundg/step : {A : tp pos} (c : ℂ) {b : cmp cost} (e : cmp (F A)) →
  IsBoundedG A e b →
  IsBoundedG A (step (F A) c e) (step cost c b)
boundg/step c {b} e h =
  let open ≲-Reasoning cost in
  begin
    bind cost (step (F _) c e) (λ _ → ret triv)
  ≡⟨⟩
    step cost c (bind cost e (λ _ → ret triv))
  ≤⟨ step-mono-≲ (≤-refl {x = c}) h ⟩
    step cost c b
  ∎

boundg/bind : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (b : val A → cmp cost) →
  ((a : val A) → IsBoundedG B (f a) (b a)) →
  IsBoundedG B (bind {A} (F B) e f) (bind {A} cost e b)
boundg/bind {e = e} {f} b hf =
  let open ≲-Reasoning cost in
  begin
    bind cost (bind (F _) e f) (λ _ → ret triv)
  ≡⟨⟩
    bind cost e (λ a → bind cost (f a) λ _ → ret triv)
  ≤⟨ bind-monoʳ-≲ e hf ⟩
    bind cost e b
  ∎

boundg/bool : ∀ {A : tp pos} {e0 e1} {p : val bool → cmp cost} →
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
  (p : cmp cost) →
  ((a : val A) → IsBoundedG (C (inj₁ a)) (e0 a) p) →
  ((b : val B) → IsBoundedG (C (inj₂ b)) (e1 b) p) →
  IsBoundedG (C s) (sum/case A B (λ s → F (C s)) s e0 e1) p
boundg/sum/case/const/const A B C s e0 e1 p h1 h2 = sum/case A B
  (λ s → meta (IsBoundedG (C s) (sum/case A B (λ s₁ → F (C s₁)) s e0 e1) p)) s h1 h2
