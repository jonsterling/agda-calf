module Examples.Sorting.Parallel.Comparable where

open import Algebra.Cost


parCostMonoid = ℕ²-ParCostMonoid
costMonoid = ParCostMonoid.costMonoid parCostMonoid

open import Data.Nat using (ℕ)
open ParCostMonoid parCostMonoid using (ℂ)
open import Data.Product using (_,_)

fromℕ : ℕ → ℂ
fromℕ n = n , n

open import Examples.Sorting.Comparable costMonoid fromℕ public
