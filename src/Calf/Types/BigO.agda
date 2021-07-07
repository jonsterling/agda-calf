{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.BigO (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid

open import Calf.Types.Nat using (nat)
open import Calf.Types.Bounded costMonoid

open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

[_]*_ : ℕ → ℂ → ℂ
[ ℕ.zero  ]* c = zero
[ ℕ.suc k ]* c = c + [ k ]* c

record BigO
  (A : tp pos) {B : tp pos}
  (∣_∣ : val A → val nat)
  (f : cmp (Π A λ _ → F B)) (g : ℕ → ℂ) : □
  where
    constructor _≤n⇒f[n]≤_g[n]via_
    field
      n' : val nat
      k : val nat
      h : ∀ x → n' Nat.≤ ∣ x ∣ → IsBounded B (f x) ([ k ]* g ∣ x ∣)

taking_measured-via_,_∈𝓞_ : (A : tp pos) {B : tp pos} (∣_∣ : val A → val nat) (f : cmp (Π A λ _ → F B)) (g : ℕ → ℂ) → □
taking A measured-via size , f ∈𝓞 g = BigO A size f g

_≤n⇒f[n]≤g[n]via_ : ∀ {A B f ∣_∣ g} → (n' : val nat) → (∀ x → n' Nat.≤ ∣ x ∣ → IsBounded B (f x) (g ∣ x ∣)) → BigO A ∣_∣ f g
n' ≤n⇒f[n]≤g[n]via h = n' ≤n⇒f[n]≤ 1 g[n]via (λ x h≤ → Eq.subst (IsBounded _ _) (Eq.sym (+-identityʳ _)) (h x h≤))
