module Calf.Value.BigO where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Calf.Computation.Tensor

IsBounded : (X : 𝒱) → U (F X) → ℂ → 𝒱
IsBounded X e c = bind {A = ⊤} e (const 0ℂ) ⊑ c

record given_measured-via_,_∈𝓞_
  (X : 𝒱) {Y : X → 𝒱}
  (∣_∣ : X → ℕ)
  (f : U ([ x ∈ X ] ⇀ F (Y x))) (g : ℕ → ℂ) : 𝒱
  where
    constructor _≤n⇒f[n]≤_g[n]via_
    field
      n' : ℕ
      k : ℕ
      h : ∀ x → n' ≤ ∣ x ∣ → IsBounded (Y x) (f x) (k ⊙ g ∣ x ∣)

_≤n⇒f[n]≤g[n]via_ : ∀ {X : 𝒱} {Y : X → 𝒱} {f ∣_∣ g} →
  (n' : ℕ) → (∀ x → n' ≤ ∣ x ∣ → IsBounded (Y x) (f x) (g ∣ x ∣)) → given X measured-via ∣_∣ , f ∈𝓞 g
_≤n⇒f[n]≤g[n]via_ {Y = Y} {f = f} n' h =
  n' ≤n⇒f[n]≤ 1 g[n]via λ x h≤ →
    subst (IsBounded (Y x) (f x)) (sym (+ℂ-identityʳ _)) (h x h≤)

f[n]≤g[n]via_ : ∀ {X : 𝒱} {Y : X → 𝒱} {f ∣_∣ g} →
  (∀ x → IsBounded (Y x) (f x) (g ∣ x ∣)) → given X measured-via ∣_∣ , f ∈𝓞 g
f[n]≤g[n]via h = 0 ≤n⇒f[n]≤g[n]via (λ x _ → h x)
