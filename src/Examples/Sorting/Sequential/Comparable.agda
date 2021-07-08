{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Sequential.Comparable where

open import Calf.CostMonoid
open import Calf.CostMonoids

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid hiding (zero; _+_; _≤_; ≤-refl; ≤-trans) public

open import Examples.Sorting.Comparable costMonoid (λ n → n) public
