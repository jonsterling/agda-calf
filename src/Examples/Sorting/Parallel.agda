{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Parallel where

open import Examples.Sorting.Parallel.Comparable

open import Calf costMonoid
open import Calf.Types.Nat
open import Calf.Types.List

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Product using (_,_)
open import Data.Nat using (z≤n; s≤s)

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module Ex/InsertionSort where
  import Examples.Sorting.Parallel.InsertionSort NatComparable as Sort

  list' = list nat

  ex/insert : cmp (F list')
  ex/insert = Sort.insert 3 (1 ∷ 2 ∷ 4 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 15 , 15

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 120 , 120

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 76 , 76

module Ex/MergeSort where
  import Examples.Sorting.Parallel.MergeSort NatComparable as Sort

  list' = list nat

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ [])

  ex/merge : cmp (F list')
  ex/merge = Sort.merge (2 ∷ 3 ∷ 6 ∷ 8 ∷ [] , 1 ∷ 5 ∷ 8 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 32, 15

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 32, 15

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 47, 26

module Ex/MergeSortPar where
  import Examples.Sorting.Parallel.MergeSortPar NatComparable as Sort

  list' = list nat

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ [])

  ex/splitMid : cmp (F Sort.triple)
  ex/splitMid = Sort.splitMid test/forward (s≤s z≤n)

  ex/splitBy : cmp (F Sort.pair)
  ex/splitBy = Sort.splitBy test/forward 5

  ex/merge : cmp (F list')
  ex/merge = Sort.merge (2 ∷ 3 ∷ 6 ∷ 8 ∷ [] , 1 ∷ 5 ∷ 8 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 40, 21

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 40, 21

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 43, 17

module SortEquivalence (M : Comparable) where
  open Comparable M
  open import Examples.Sorting.Parallel.Core M

  import Examples.Sorting.Parallel.InsertionSort M as ISort
  import Examples.Sorting.Parallel.MergeSort     M as MSort
  import Examples.Sorting.Parallel.MergeSortPar  M as PSort

  isort≡msort : ◯ (ISort.sort ≡ MSort.sort)
  isort≡msort = IsSort⇒≡ ISort.sort ISort.sort/correct MSort.sort MSort.sort/correct

  msort≡psort : ◯ (MSort.sort ≡ PSort.sort)
  msort≡psort = IsSort⇒≡ MSort.sort MSort.sort/correct PSort.sort PSort.sort/correct
