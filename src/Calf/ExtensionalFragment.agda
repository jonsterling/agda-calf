{-# OPTIONS --prop --without-K --rewriting #-}

-- Extensional fragment.

open import Calf.CostMonoid

module Calf.ExtensionalFragment (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Eq
open import Calf.Step costMonoid

open import Data.Product
open import Relation.Binary.PropositionalEquality as P


postulate
  step/ext : ∀ X → (e : cmp X) → (c : ℂ) → ◯ (step X c e ≡ e)
  -- sadly the above cannot be made an Agda rewrite rule