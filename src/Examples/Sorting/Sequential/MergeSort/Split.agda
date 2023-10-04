{-# OPTIONS --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.MergeSort.Split (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid hiding (A)
open import Calf.Data.Product
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.IsBoundedG costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Properties as N using (module ≤-Reasoning)


pair = list A ×⁺ list A

split/type : val nat → val nat → val (list A) → tp pos
split/type k k' l = Σ⁺ pair λ (l₁ , l₂) → meta⁺ (length l₁ ≡ k × length l₂ ≡ k' × l ↭ (l₁ ++ l₂))

split/clocked : cmp (Π nat λ k → Π nat λ k' → Π (list A) λ l → Π (meta⁺ (k + k' ≡ length l)) λ _ → F (split/type k k' l))
split/clocked zero    k' l        refl = ret (([] , l) , refl , refl , refl)
split/clocked (suc k) k' (x ∷ xs) h    =
  bind (F (split/type (suc k) k' (x ∷ xs))) (split/clocked k k' xs (N.suc-injective h)) λ ((l₁ , l₂) , h₁ , h₂ , xs↭l₁++l₂) →
  ret ((x ∷ l₁ , l₂) , Eq.cong suc h₁ , h₂ , prep x xs↭l₁++l₂)

split/clocked/total : ∀ k k' l h → IsValuable (split/clocked k k' l h)
split/clocked/total zero    k' l        refl u = ↓ refl
split/clocked/total (suc k) k' (x ∷ xs) h    u
  rewrite Valuable.proof (split/clocked/total k k' xs (N.suc-injective h) u) = ↓ refl

split/clocked/cost : cmp (Π nat λ k → Π nat λ k' → Π (list A) λ l → Π (meta⁺ (k + k' ≡ length l)) λ _ → F unit)
split/clocked/cost _ _ _ _ = step⋆ zero

split/clocked/is-bounded : ∀ k k' l h → IsBoundedG (split/type k k' l) (split/clocked k k' l h) (split/clocked/cost k k' l h)
split/clocked/is-bounded zero    k' l        refl = ≤⁻-refl
split/clocked/is-bounded (suc k) k' (x ∷ xs) h    = bind-monoˡ-≤⁻ _ (split/clocked/is-bounded k k' xs (N.suc-injective h))


split : cmp (Π (list A) λ l → F (split/type ⌊ length l /2⌋ ⌈ length l /2⌉ l))
split l = split/clocked ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

split/total : ∀ l → IsValuable (split l)
split/total l = split/clocked/total ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

split/cost : cmp (Π (list A) λ _ → F unit)
split/cost l = split/clocked/cost ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

split/is-bounded : ∀ l → IsBoundedG (split/type ⌊ length l /2⌋ ⌈ length l /2⌉ l) (split l) (split/cost l)
split/is-bounded l = split/clocked/is-bounded ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))
