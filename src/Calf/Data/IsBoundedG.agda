{-# OPTIONS --prop --rewriting #-}

open import Algebra.Cost

-- Upper bound on the cost of a computation.

module Calf.Data.IsBoundedG (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid
open import Calf.Data.Product using (unit)


cost : tp⁻
cost = F unit

-- (e ; ret triv) ≤⁻ b
IsBoundedG : (A : tp⁺) → cmp (F A) → cmp cost → Set
IsBoundedG A e b = (bind cost e λ _ → ret triv) ≤⁻[ cost ] b

step⋆ : cmp (Π ℂ⁺ λ _ → cost)
step⋆ c = step cost c (ret triv)

step⋆-mono-≤⁻ : {c c' : ℂ} → c ≤ c' → step⋆ c ≤⁻[ cost ] step⋆ c'
step⋆-mono-≤⁻ = step-monoˡ-≤⁻ (ret triv)


boundg/relax : {b b' : cmp cost}
  → b ≤⁻[ cost ] b'
  → {e : cmp (F A)}
  → IsBoundedG A e b
  → IsBoundedG A e b'
boundg/relax {b = b} {b'} h {e = e} ib-b =
  let open ≤⁻-Reasoning cost in
  begin
    bind cost e (λ _ → ret triv)
  ≲⟨ ib-b ⟩
    b
  ≲⟨ h ⟩
    b'
  ∎

boundg/step : (c : ℂ) {b : cmp cost} (e : cmp (F A)) →
  IsBoundedG A e b →
  IsBoundedG A (step (F A) c e) (step cost c b)
boundg/step c {b} e h =
  let open ≤⁻-Reasoning cost in
  begin
    bind cost (step (F _) c e) (λ _ → ret triv)
  ≡⟨⟩
    step cost c (bind cost e (λ _ → ret triv))
  ≲⟨ step-monoʳ-≤⁻ c h ⟩
    step cost c b
  ∎

boundg/bind : {e : cmp (F A)} {f : val A → cmp (F B)}
  (b : val A → cmp cost) →
  ((a : val A) → IsBoundedG B (f a) (b a)) →
  IsBoundedG B (bind {A} (F B) e f) (bind {A} cost e b)
boundg/bind {e = e} {f} b hf =
  let open ≤⁻-Reasoning cost in
  begin
    bind cost (bind (F _) e f) (λ _ → ret triv)
  ≡⟨⟩
    bind cost e (λ a → bind cost (f a) λ _ → ret triv)
  ≲⟨ bind-monoʳ-≤⁻ e hf ⟩
    bind cost e b
  ∎
