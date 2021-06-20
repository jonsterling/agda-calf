{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting where

open import Calf
open import Calf.Types.List as List

open import Examples.Sorting.Comparable

open import Relation.Binary.PropositionalEquality as Eq using (module ≡-Reasoning)
open import Data.Nat using (ℕ)

import Examples.Sorting.InsertionSort as InsertionSort
import Examples.Sorting.MergeSort     as MergeSort

module SortEquivalence (M : Comparable) where
  open Comparable M
  open import Examples.Sorting.Core M

  module ISort = InsertionSort M
  module MSort = MergeSort M

  isort≡msort : ◯ (ISort.sort ≡ MSort.sort)
  isort≡msort u =
    funext λ l →
      let (l'ᵢ , ≡ᵢ , ↭ᵢ , sortedᵢ) = ISort.sort/correct l u in
      let (l'ₘ , ≡ₘ , ↭ₘ , sortedₘ) = MSort.sort/correct l u in
      begin
        ISort.sort l
      ≡⟨ ≡ᵢ ⟩
        ret l'ᵢ
      ≡⟨ Eq.cong ret (unique-sorted sortedᵢ sortedₘ (trans (↭-sym ↭ᵢ) ↭ₘ)) ⟩
        ret l'ₘ
      ≡˘⟨ ≡ₘ ⟩
        MSort.sort l
      ∎
        where open ≡-Reasoning

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module Ex/InsertionSort where
  module Sort = InsertionSort NatComparable

  list' = list (U (meta ℕ))

  ex/insert : cmp (F list')
  ex/insert = Sort.insert 3 (1 ∷ 2 ∷ 4 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 15

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 120

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 76

module Ex/MergeSort where
  module Sort = MergeSort NatComparable

  list' = list (U (meta ℕ))

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ [])

  ex/merge : cmp (F list')
  ex/merge = Sort.merge (2 ∷ 3 ∷ 6 ∷ 8 ∷ [] , 1 ∷ 5 ∷ 8 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 32

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 32

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 47
