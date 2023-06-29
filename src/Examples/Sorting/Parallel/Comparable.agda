module Examples.Sorting.Parallel.Comparable where

open import Calf.CostMonoid
open import Calf.CostMonoids

parCostMonoid = ℕ²-ParCostMonoid
costMonoid = ParCostMonoid.costMonoid parCostMonoid

open import Data.Nat using (ℕ)
open ParCostMonoid parCostMonoid using (ℂ)
open import Data.Product using (_,_)

fromℕ : ℕ → ℂ
fromℕ n = n , n

open import Examples.Sorting.Comparable costMonoid fromℕ public
