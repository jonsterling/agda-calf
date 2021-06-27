{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.Nat (costMonoid : CostMonoid) where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction costMonoid
open import Calf.Upper costMonoid
open import Calf.Eq
open import Calf.BoundedFunction costMonoid
open import Data.Nat as Nat using (ℕ ; _+_)
open import Function
open import Relation.Binary.PropositionalEquality as P

nat : tp pos
nat = U (meta ℕ)

zero : val nat
zero = Nat.zero

succ : val nat → val nat
succ = Nat.suc

rec : (n : val nat) → (X : (n : val nat) → tp neg) → cmp (X zero) → ((n : val nat) → (cmp (X n)) → cmp (X (succ n))) →
  cmp (X n)
rec Nat.zero    X bc is = bc
rec (Nat.suc n) X bc is = is n (rec n X bc is)

toℕ : val nat → ℕ
toℕ n = n

tonat : ℕ → val nat
tonat n = n
