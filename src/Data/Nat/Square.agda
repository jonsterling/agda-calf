{-# OPTIONS --prop --without-K #-}

module Data.Nat.Square where

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

_² : ℕ → ℕ
n ² = n * n

n^2≡n² : ∀ n → n ^ 2 ≡ n ²
n^2≡n² n = Eq.cong (n *_) (*-identityʳ n)

²-mono : _² Preserves _≤_ ⟶ _≤_
²-mono m≤n = *-mono-≤ m≤n m≤n
