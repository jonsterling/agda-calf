{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.Core (M : Comparable) where

open Comparable M

open import Calf costMonoid
open import Calf.Types.List

open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as N

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
unique-sorted []             (h₂ ∷ sorted₂) ↭ = contradiction (↭-sym ↭) ¬x∷xs↭[]
unique-sorted (h₁ ∷ sorted₁) []             ↭ = contradiction (↭) ¬x∷xs↭[]
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

IsSort⇒≡ : ∀ sort₁ → IsSort sort₁ → ∀ sort₂ → IsSort sort₂ → ◯ (sort₁ ≡ sort₂)
IsSort⇒≡ sort₁ correct₁ sort₂ correct₂ u =
  funext λ l →
    let (l'₁ , ≡₁ , ↭₁ , sorted₁) = correct₁ l u in
    let (l'₂ , ≡₂ , ↭₂ , sorted₂) = correct₂ l u in
    begin
      sort₁ l
    ≡⟨ ≡₁ ⟩
      ret l'₁
    ≡⟨ Eq.cong ret (unique-sorted sorted₁ sorted₂ (trans (↭-sym ↭₁) ↭₂)) ⟩
      ret l'₂
    ≡˘⟨ ≡₂ ⟩
      sort₂ l
    ∎
      where open ≡-Reasoning
