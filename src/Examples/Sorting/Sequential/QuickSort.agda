{-# OPTIONS --allow-unsolved-metas #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.QuickSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid
open import Calf.Probability costMonoid
open import Calf.Types.Product
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.BoundedG costMonoid
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_$_)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_)
import Data.Nat.Properties as N
open import Data.Nat.Square

choose : cmp $ Π (list A) λ l → Π (meta⁺ (length l Nat.> 0)) λ _ → F (prod⁺ A (list A))
choose (x ∷ [])         h = ret (x , [])
choose (x ∷ xs@(_ ∷ _)) h =
  flip (F (prod⁺ A (list A))) (1 / length (x ∷ xs))
    (bind (F (prod⁺ A (list A))) (choose xs (Nat.s≤s Nat.z≤n)) λ (y , ys) → ret (y , x ∷ ys))
    (ret (x , xs))

partition : cmp $ Π A λ _ → Π (list A) λ _ → F (prod⁺ (list A) (list A))
partition pivot []       = ret ([] , [])
partition pivot (x ∷ xs) =
  bind (F (prod⁺ (list A) (list A))) (partition pivot xs) λ (xs₁ , xs₂) →
  bind (F (prod⁺ (list A) (list A))) (x ≤? pivot) λ
    { (yes p) → ret (x ∷ xs₁ , xs₂)
    ; (no ¬p) → ret (xs₁ , x ∷ xs₂)
    }

sort/clocked : cmp $ Π nat λ k → Π (list A) λ l → Π (meta⁺ (length l Nat.≤ k)) λ _ → F (list A)
sort/clocked k []             h = ret []
sort/clocked (suc k) (x ∷ xs) h =
  bind (F (list A)) (choose (x ∷ xs) (Nat.s≤s Nat.z≤n)) λ (pivot , l) →
  bind (F (list A)) (partition pivot l) λ (l₁ , l₂) →
  bind (F (list A)) (sort/clocked k l₁ {!   !}) λ l₁' →
  bind (F (list A)) (sort/clocked k l₂ {!   !}) λ l₂' →
  ret (l₁' ++ [ pivot ] ++ l₂')

sort : cmp $ Π (list A) λ _ → F (list A)
sort l = sort/clocked (length l) l N.≤-refl
