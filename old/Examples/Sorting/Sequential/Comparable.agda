{-# OPTIONS --rewriting #-}

module Examples.Sorting.Sequential.Comparable where

open import Algebra.Cost public


costMonoid = ℕ-CostMonoid

open import Data.Nat using (ℕ)
open CostMonoid costMonoid using (ℂ)

fromℕ : ℕ → ℂ
fromℕ n = n

open import Examples.Sorting.Comparable costMonoid fromℕ public
