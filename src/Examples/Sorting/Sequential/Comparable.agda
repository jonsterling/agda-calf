{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Sequential.Comparable where

open import Calf.CostMonoid
open import Calf.CostMonoids

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid hiding (zero; _+_; _≤_; ≤-refl; ≤-trans) public

open import Data.Nat using (ℕ)

fromℕ : ℕ → ℂ
fromℕ n = n

open import Examples.Sorting.Comparable costMonoid fromℕ public
