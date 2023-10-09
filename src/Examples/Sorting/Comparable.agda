{-# OPTIONS --rewriting #-}

open import Algebra.Cost
open import Data.Nat using (ℕ)

module Examples.Sorting.Comparable
  (costMonoid : CostMonoid) (fromℕ : ℕ → CostMonoid.ℂ costMonoid) where

open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid hiding (A)
open import Calf.Data.Bool using (bool)
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.Product using (∃)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Reflects
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Sum
open import Function


record Comparable : Set₁ where
  field
    A : tp⁺
    _≤_ : val A → val A → Set
    ≤-refl : Reflexive _≤_
    ≤-trans : Transitive _≤_
    ≤-total : Total _≤_
    ≤-antisym : Antisymmetric _≡_ _≤_
    _≤?_ : cmp (Π A λ x → Π A λ y → F (meta⁺ (Dec (x ≤ y))))
    ≤?-total : (x y : val A) → ◯ (∃ λ p → x ≤? y ≡ ret p)
    h-cost : (x y : val A) → IsBounded (meta⁺ (Dec (x ≤ y))) (x ≤? y) (fromℕ 1)

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ ¬x≤y with ≤-total _ _
  ... | inj₁ x≤y = contradiction x≤y ¬x≤y
  ... | inj₂ y≤x = y≤x

  case-≤ : {S : Set} {x y : val A} → (x ≤ y → S) → (x ≰ y → S) → Dec (x ≤ y) → S
  case-≤ {S} {x} {y} yes-branch no-branch (yes x≤y) = yes-branch x≤y
  case-≤ {S} {x} {y} yes-branch no-branch (no ¬x≤y) = no-branch ¬x≤y

  bind/case-≤ : {x y : val A} {f : val B → cmp X} (yes-branch : x ≤ y → cmp (F B)) (no-branch : x ≰ y → cmp (F B)) (d : Dec (x ≤ y)) →
    bind X (case-≤ yes-branch no-branch d) f ≡ case-≤ (λ h → bind X (yes-branch h) f) (λ h → bind X (no-branch h) f) d
  bind/case-≤ yes-branch no-branch (yes x≤y) = refl
  bind/case-≤ yes-branch no-branch (no ¬x≤y) = refl

  case-≤/idem : {S : Set} {x y : val A} (branch : S) (d : Dec (x ≤ y)) →
    case-≤ {S} {x} {y} (λ _ → branch) (λ _ → branch) d ≡ branch
  case-≤/idem branch (yes x≤y) = refl
  case-≤/idem branch (no ¬x≤y) = refl

NatComparable : Comparable
NatComparable = record
  { A = nat
  ; _≤_ = _≤_
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; _≤?_ = λ x y → step (F (meta⁺ (Dec (x ≤ y)))) (fromℕ 1) (ret (x ≤? y))
  ; ≤?-total = λ x y u → (x ≤? y) , (step/ext (F _) (ret _) (fromℕ 1) u)
  ; h-cost = λ _ _ → ≤⁻-refl
  }
  where
    open import Calf.Data.Nat
    open import Data.Nat.Properties
