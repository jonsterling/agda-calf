open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.Core (M : Comparable) where

open import Calf.CostMonoid
open ParCostMonoid parCostMonoid
  hiding (costMonoid)
  renaming (
    _≤_ to _≤ₚ_;
    ≤-refl to ≤ₚ-refl;
    ≤-trans to ≤ₚ-trans;
    module ≤-Reasoning to ≤ₚ-Reasoning
  ) public

open import Examples.Sorting.Core costMonoid fromℕ M public
