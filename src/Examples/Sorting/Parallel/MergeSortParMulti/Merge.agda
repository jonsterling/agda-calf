{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.MergeSortParMulti.Merge (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉; pred; _⊔_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Nat.Log2
open import Data.Nat.PredExp2


open import Examples.Sorting.Parallel.MergeSort.Split M


triple = Σ++ (list A) λ _ → Σ++ A λ _ → (list A)

splitMid/clocked : cmp (Π nat λ k → Π (list A) λ l → Π (U (meta (k Nat.< length l))) λ _ → F triple)
splitMid/clocked zero    (x ∷ xs) (s≤s h) = ret ([] , x , xs)
splitMid/clocked (suc k) (x ∷ xs) (s≤s h) =
  bind (F triple) (splitMid/clocked k xs h) λ (l₁ , mid , l₂) → ret ((x ∷ l₁) , mid , l₂)

splitMid/clocked/correct : ∀ k k' l h → k + suc k' ≡ length l →
  ◯ (∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → splitMid/clocked k l h ≡ ret (l₁ , mid , l₂) × length l₁ ≡ k × length l₂ ≡ k' × l ≡ (l₁ ++ [ mid ] ++ l₂))
splitMid/clocked/correct zero    k' (x ∷ xs) (s≤s h) refl     u = [] , x , xs , refl , refl , refl , refl
splitMid/clocked/correct (suc k) k' (x ∷ xs) (s≤s h) h-length u =
  let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct k k' xs h (N.suc-injective h-length) u in
  x ∷ l₁ , mid , l₂ , Eq.cong (λ e → bind (F triple) e _) ≡ , Eq.cong suc h₁ , h₂ , Eq.cong (x ∷_) ≡-↭

splitMid/clocked/cost : cmp (Π nat λ k → Π (list A) λ l → Π (U (meta (k Nat.< length l))) λ _ → cost)
splitMid/clocked/cost _ _ _ = 𝟘

splitMid/clocked≤splitMid/clocked/cost : ∀ k l h → IsBounded triple (splitMid/clocked k l h) (splitMid/clocked/cost k l h)
splitMid/clocked≤splitMid/clocked/cost zero    (x ∷ xs) (s≤s h) = bound/ret
splitMid/clocked≤splitMid/clocked/cost (suc k) (x ∷ xs) (s≤s h) =
  bound/bind/const 𝟘 𝟘 (splitMid/clocked≤splitMid/clocked/cost k xs h) λ _ → bound/ret

splitMid : cmp (Π (list A) λ l → Π (U (meta (0 Nat.< length l))) λ _ → F triple)
splitMid (x ∷ xs) (s≤s h) = splitMid/clocked ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)

splitMid/correct : ∀ l h →
  ◯ (∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → splitMid l h ≡ ret (l₁ , mid , l₂) × length l₁ Nat.≤ ⌊ length l /2⌋ × length l₂ Nat.≤ ⌊ length l /2⌋ × l ≡ (l₁ ++ [ mid ] ++ l₂))
splitMid/correct (x ∷ xs) (s≤s h) u =
  let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct ⌊ length (x ∷ xs) /2⌋ ⌊ pred (length (x ∷ xs)) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)
                                              (let open ≡-Reasoning in
                                              begin
                                                ⌊ length (x ∷ xs) /2⌋ + suc ⌊ pred (length (x ∷ xs)) /2⌋
                                              ≡⟨⟩
                                                ⌊ length (x ∷ xs) /2⌋ + suc ⌊ length xs /2⌋
                                              ≡⟨⟩
                                                ⌈ length xs /2⌉ + suc ⌊ length xs /2⌋
                                              ≡⟨ N.+-suc ⌈ length xs /2⌉ ⌊ length xs /2⌋ ⟩
                                                suc (⌈ length xs /2⌉ + ⌊ length xs /2⌋)
                                              ≡⟨ Eq.cong suc (N.+-comm ⌈ length xs /2⌉ ⌊ length xs /2⌋) ⟩
                                                suc (⌊ length xs /2⌋ + ⌈ length xs /2⌉)
                                              ≡⟨ Eq.cong suc (N.⌊n/2⌋+⌈n/2⌉≡n (length xs)) ⟩
                                                suc (length xs)
                                              ≡⟨⟩
                                                length (x ∷ xs)
                                              ∎) u in
  l₁ , mid , l₂ , ≡ , N.≤-reflexive h₁ , (
    let open ≤-Reasoning in
    begin
      length l₂
    ≡⟨ h₂ ⟩
      ⌊ pred (length (x ∷ xs)) /2⌋
    ≤⟨ N.⌊n/2⌋-mono N.pred[n]≤n ⟩
      ⌊ length (x ∷ xs) /2⌋
    ∎
  ), ≡-↭

splitMid/cost : cmp (Π (list A) λ l → Π (U (meta (0 Nat.< length l))) λ _ → cost)
splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)

splitMid≤splitMid/cost : ∀ l h → IsBounded triple (splitMid l h) (splitMid/cost l h)
splitMid≤splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked≤splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)


pairs = Σ++ pair λ _ → pair

bisplit : cmp (Π (list A) λ _ → Π (list A) λ _ → Π nat λ _ → F pairs)
bisplit = {!   !}


merge : cmp (Π pair λ _ → F (list A))
merge = {!   !}

merge/correct : ∀ l₁ l₂ →
  ◯ (∃ λ l → merge (l₁ , l₂) ≡ ret l × (Sorted l₁ → Sorted l₂ → SortedOf (l₁ ++ l₂) l))
merge/correct = {!   !}

merge/cost : cmp (Π pair λ _ → cost)
merge/cost = {!   !}

merge/cost/closed : cmp (Π pair λ _ → cost)
merge/cost/closed = {!   !}

merge≤merge/cost : ∀ l₁ l₂ → IsBounded (list A) (merge (l₁ , l₂)) (merge/cost (l₁ , l₂))
merge≤merge/cost = {!   !}

merge≤merge/cost/closed : ∀ l₁ l₂ → IsBounded (list A) (merge (l₁ , l₂)) (merge/cost/closed (l₁ , l₂))
merge≤merge/cost/closed = {!   !}
