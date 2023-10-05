{-# OPTIONS --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.Core (M : Comparable) where

open import Algebra.Cost
open CostMonoid costMonoid
  hiding (zero; _+_; _≤_; ≤-refl; ≤-trans) public

open import Examples.Sorting.Core costMonoid fromℕ M public
