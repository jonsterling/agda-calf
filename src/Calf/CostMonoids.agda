{-# OPTIONS --prop --without-K --rewriting #-}

-- Common cost monoids.

module Calf.CostMonoids where

open import Calf.CostMonoid

ℕ-CostMonoid : CostMonoid
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; _≤_ = _≤_
  ; isCostMonoid = record
      { isCommutativeMonoid = +-0-isCommutativeMonoid
      ; isTotalPreorder = ≤-isTotalPreorder
      ; +-mono-≤ = +-mono-≤
      ; z≤c = z≤n
      }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality
