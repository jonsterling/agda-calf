{-# OPTIONS --prop --rewriting #-}

module Calf.Nat where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Upper
open import Calf.Eq
open import Data.Nat as Nat using (ℕ ; _+_)
open import Calf.Connectives
open import Function
open import Relation.Binary.PropositionalEquality as P

open Ext
open iso

postulate
  nat : tp pos
  zero : val nat
  succ : val nat → val nat
  rec : (n : val nat) → (X : (n : val nat) → tp neg) → cmp (X zero) → ((n : val nat) → (cmp (X n)) → cmp (X (succ n))) →
    cmp (X n)
  rec/zero : ∀ {X e0 e1} → rec zero X e0 e1 ≡ e0
  rec/succ : ∀ {n X e0 e1} → rec (succ n) X e0 e1 ≡ e1 n (rec n X e0 e1)
  {-# REWRITE rec/zero rec/succ #-}

-- Converting nat to ℕ
-- Better to keep these as postulates so some equations are rewritten automatically
postulate
  toℕ : val nat → ℕ
  tonat : ℕ → val nat
  ℕ-nat : ∀ x → tonat (toℕ x) ≡ x
  nat-ℕ : ∀ n → toℕ (tonat n) ≡ n
  toℕ-zero : toℕ zero ≡ 0
  toℕ-succ : ∀ {x} → toℕ (succ x) ≡ Nat.suc (toℕ x)
  {-# REWRITE nat-ℕ ℕ-nat toℕ-zero toℕ-succ #-}

e/nat : Ext nat
e/nat = record
  { Carrier = ℕ
  ; rep = record { fwd = toℕ ; bwd = tonat ; bwd-fwd = ℕ-nat ; fwd-bwd = nat-ℕ }
  }

-- toℕ : val nat → ℕ
-- toℕ n = rec n (λ _ → meta ℕ) 0 (λ _ r → 1 + r)

-- tonat : ℕ → val nat
-- tonat 0 = zero
-- tonat (Nat.suc n) = succ (tonat n)
