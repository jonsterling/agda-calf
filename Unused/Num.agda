{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Upper
open import Eq
open import Data.Nat as Nat
open import Connectives
open import Function
open import Relation.Binary.PropositionalEquality as P

open Ext
open iso

postulate
  num : tp pos
  to-nat : val num → ℕ
  to-num : ℕ → val num
  nat-num : ∀ x → to-num (to-nat x) ≡ x
  num-nat : ∀ n → to-nat (to-num n) ≡ n
  {-# REWRITE nat-num num-nat #-}

e/num : Ext num
e/num = record
  { Carrier = ℕ
  ; rep = record { fwd = to-nat ; bwd = to-num ; bwd-fwd = nat-num ; fwd-bwd = num-nat }
  }

postulate
  ifz :
    (B : ℕ → tp neg) →
    (x : val num) →
    cmp (B 0) →
    ((y : val num) → suc (to-nat y) ≡ to-nat x → cmp (B (suc (to-nat y)))) →
    cmp (B (to-nat x))

  ifz/zero : ∀ {B} →
    (c0 : cmp (B 0)) →
    (c1 : (y : val num) → suc (to-nat y) ≡ 0 → cmp (B (suc (to-nat y)))) →
    (ifz B (to-num 0) c0 c1) ≡ c0
  {-# REWRITE ifz/zero #-}

  ifz/suc : ∀ {B} →
    (n : ℕ) →
    (c0 : cmp (B 0)) →
    (c1 : (y : val num) → suc (to-nat y) ≡ suc n → cmp (B (suc (to-nat y)))) →
    ifz B (to-num (suc n)) c0 c1 ≡ c1 (to-num n) refl
  {-# REWRITE ifz/suc #-}

