{-# OPTIONS --without-K --prop --rewriting #-}

module Calf.Types.Nat where

open import Calf.Prelude
open import Calf.Metalanguage
open import Data.Nat as Nat using (ℕ)

nat : tp pos
nat = meta ℕ

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
