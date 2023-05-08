{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Sequential.Comparable where

open import Calf.CostMonoid public
open import Calf.CostMonoids
open import Calf.PhaseDistinction

costMonoid = ◯-CostMonoid ℕ-CostMonoid

open import Data.Nat using (ℕ)
open CostMonoid costMonoid using (ℂ)

fromℕ : ℕ → ℂ
fromℕ n = λ _ → n

open import Examples.Sorting.Comparable costMonoid fromℕ public
