{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Parallel.Comparable where

open import Calf.CostMonoid
open import Calf.CostMonoids

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid
  renaming (
    _≤_ to _≤ₚ_;
    ≤-refl to ≤ₚ-refl;
    ≤-trans to ≤ₚ-trans;
    module ≤-Reasoning to ≤ₚ-Reasoning
  ) public

open import Data.Product using (_,_)
open import Examples.Sorting.Comparable costMonoid (λ n → n , n) public
