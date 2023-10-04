{-# OPTIONS --rewriting #-}

-- Big-O bound on the cost of a computation.

open import Algebra.Cost

module Calf.Data.BigO (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Step costMonoid

open import Calf.Data.Nat as Nat using (nat; ℕ)
open import Calf.Data.IsBounded costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

[_]*_ : ℕ → ℂ → ℂ
[ ℕ.zero  ]* c = zero
[ ℕ.suc k ]* c = c + [ k ]* c

record given_measured-via_,_∈𝓞_
  (A : tp pos) {B : val A → tp pos}
  (∣_∣ : val A → val nat)
  (f : cmp (Π A λ a → F (B a))) (g : ℕ → ℂ) : □
  where
    constructor _≤n⇒f[n]≤_g[n]via_
    field
      n' : val nat
      k : val nat
      h : ∀ a → n' Nat.≤ ∣ a ∣ → IsBounded (B a) (f a) ([ k ]* g ∣ a ∣)

_≤n⇒f[n]≤g[n]via_ : ∀ {A : tp pos} {B : val A → tp pos} {f ∣_∣ g} →
  (n' : val nat) → (∀ a → n' Nat.≤ ∣ a ∣ → IsBounded (B a) (f a) (g ∣ a ∣)) → given A measured-via ∣_∣ , f ∈𝓞 g
_≤n⇒f[n]≤g[n]via_ {B = B} {f = f} n' h =
  n' ≤n⇒f[n]≤ 1 g[n]via λ a h≤ →
    Eq.subst (IsBounded (B a) (f a)) (Eq.sym (+-identityʳ _)) (h a h≤)

f[n]≤g[n]via_ : ∀ {A : tp pos} {B : val A → tp pos} {f ∣_∣ g} →
  (∀ a → IsBounded (B a) (f a) (g ∣ a ∣)) → given A measured-via ∣_∣ , f ∈𝓞 g
f[n]≤g[n]via h = 0 ≤n⇒f[n]≤g[n]via (λ a _ → h a)
