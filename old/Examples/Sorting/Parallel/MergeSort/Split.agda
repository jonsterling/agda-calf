open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.MergeSort.Split (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.Parallel parCostMonoid
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.IsBounded costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Properties as N using (module ≤-Reasoning)


pair = Σ⁺ (list A) λ _ → (list A)

split/clocked : cmp (Π nat λ _ → Π (list A) λ _ → F pair)
split/clocked zero    l        = ret ([] , l)
split/clocked (suc k) []       = ret ([] , [])
split/clocked (suc k) (x ∷ xs) = bind (F pair) (split/clocked k xs) λ (l₁ , l₂) → ret (x ∷ l₁ , l₂)

split/clocked/correct : ∀ k k' l → k + k' ≡ length l →
  ◯ (∃ λ l₁ → ∃ λ l₂ → split/clocked k l ≡ ret (l₁ , l₂) × length l₁ ≡ k × length l₂ ≡ k' × l ↭ (l₁ ++ l₂))
split/clocked/correct zero    k' l        refl u = [] , l , refl , refl , refl , refl
split/clocked/correct (suc k) k' (x ∷ xs) h    u =
  let (l₁ , l₂ , ≡ , h₁ , h₂ , ↭) = split/clocked/correct k k' xs (N.suc-injective h) u in
  x ∷ l₁ , l₂ , Eq.cong (λ e → bind (F pair) e λ (l₁ , l₂) → ret (x ∷ l₁ , l₂)) ≡ , Eq.cong suc h₁ , h₂ , prep x ↭

split/clocked/cost : cmp (Π nat λ _ → Π (list A) λ _ → cost)
split/clocked/cost _ _ = 𝟘

split/clocked≤split/clocked/cost : ∀ k l → IsBounded pair (split/clocked k l) (split/clocked/cost k l)
split/clocked≤split/clocked/cost zero    l        = bound/ret
split/clocked≤split/clocked/cost (suc k) []       = bound/ret
split/clocked≤split/clocked/cost (suc k) (x ∷ xs) = bound/bind/const 𝟘 𝟘 (split/clocked≤split/clocked/cost k xs) λ (l₁ , l₂) → bound/ret {a = x ∷ l₁ , l₂}

split : cmp (Π (list A) λ _ → F pair)
split l = split/clocked ⌊ length l /2⌋ l

split/correct : ∀ l →
  ◯ (∃ λ l₁ → ∃ λ l₂ → split l ≡ ret (l₁ , l₂) × length l₁ ≡ ⌊ length l /2⌋ × length l₂ ≡ ⌈ length l /2⌉ × l ↭ (l₁ ++ l₂))
split/correct l = split/clocked/correct ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

split/cost : cmp (Π (list A) λ _ → cost)
split/cost l = split/clocked/cost ⌊ length l /2⌋ l

split≤split/cost : ∀ l → IsBounded pair (split l) (split/cost l)
split≤split/cost l = split/clocked≤split/clocked/cost ⌊ length l /2⌋ l
