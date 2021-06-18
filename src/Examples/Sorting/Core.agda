{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Comparable using (Comparable)

module Examples.Sorting.Core (M : Comparable) where

open Comparable M

open import Calf
open import Calf.Types.List as List

open import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat as Nat using (s≤s)
open import Data.Empty

open import Data.List.Relation.Binary.Permutation.Propositional public
open import Data.List.Relation.Binary.Permutation.Propositional.Properties renaming (++⁺ to ++⁺-↭) public
open import Data.List.Relation.Unary.All public
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺-All) public
open import Data.List.Relation.Unary.Any using (Any; here; there)

_≤*_ : val A → val (list A) → Set
_≤*_ x = All (x ≤_)

≤-≤* : ∀ {x₁ x₂ l} → x₁ ≤ x₂ → x₂ ≤* l → x₁ ≤* l
≤-≤* x₁≤x₂ = map (≤-trans x₁≤x₂)

data Sorted : val (list A) → Set where
  [] : Sorted []
  _∷_ : ∀ {y ys} → y ≤* ys → Sorted ys → Sorted (y ∷ ys)

short-sorted : {l : val (list A)} → length l Nat.≤ 1 → Sorted l
short-sorted {[]} _ = []
short-sorted {_ ∷ []} _ = [] ∷ []
short-sorted {_ ∷ _ ∷ _} (s≤s ())

unique-sorted : ∀ {l'₁ l'₂} → Sorted l'₁ → Sorted l'₂ → l'₁ ↭ l'₂ → l'₁ ≡ l'₂
unique-sorted []             []             ↭ = refl
unique-sorted []             (h₂ ∷ sorted₂) ↭ = ⊥-elim (¬x∷xs↭[] (↭-sym ↭))
unique-sorted (h₁ ∷ sorted₁) []             ↭ = ⊥-elim (¬x∷xs↭[] ↭)
unique-sorted (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) ↭ with
  ≤-antisym
    (lookup (≤-refl ∷ h₁) (Any-resp-↭ (↭-sym ↭) (here refl)))
    (lookup (≤-refl ∷ h₂) (Any-resp-↭ (↭) (here refl)))
... | refl = Eq.cong (_ ∷_) (unique-sorted sorted₁ sorted₂ (drop-∷ ↭))

SortedOf : val (list A) → val (list A) → Set
SortedOf l l' = l ↭ l' × Sorted l'

SortResult : cmp (Π (list A) λ _ → F (list A)) → val (list A) → Set
SortResult sort l = ◯ (∃ λ l' → sort l ≡ ret l' × SortedOf l l')

IsSort : cmp (Π (list A) λ _ → F (list A)) → Set
IsSort sort = ∀ l → SortResult sort l
