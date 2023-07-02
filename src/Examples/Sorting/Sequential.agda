module Examples.Sorting.Sequential where

open import Examples.Sorting.Sequential.Comparable

open import Calf costMonoid
open import Calf.Types.Nat
open import Calf.Types.List

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Product using (_,_)

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module Ex/InsertionSort where
  import Examples.Sorting.Sequential.InsertionSort NatComparable as Sort

  ex/insert = Sort.insert 3 (1 ∷ 2 ∷ 4 ∷ [])
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])
  ex/sort/forward = Sort.sort test/forward  -- cost: 15
  ex/sort/backward = Sort.sort test/backward  -- cost: 120
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 76

module Ex/MergeSort where
  import Examples.Sorting.Sequential.MergeSort NatComparable as Sort

  ex/split = Sort.split (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ [])
  ex/merge = Sort.merge (2 ∷ 3 ∷ 6 ∷ 8 ∷ [] , 1 ∷ 5 ∷ 8 ∷ [])
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])
  ex/sort/forward = Sort.sort test/forward  -- cost: 32
  ex/sort/backward = Sort.sort test/backward  -- cost: 32
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 47

module SortEquivalence (M : Comparable) where
  open Comparable M
  open import Examples.Sorting.Sequential.Core M

  import Examples.Sorting.Sequential.InsertionSort M as ISort
  import Examples.Sorting.Sequential.MergeSort     M as MSort

  isort≡msort : ◯ (ISort.sort algorithm ≡ MSort.sort algorithm)
  isort≡msort = IsSort⇒≡ ISort.sort ISort.sort/total MSort.sort MSort.sort/total
