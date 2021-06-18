{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Comparable where

open import Calf
open import Calf.Types.Bool

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq
open import Function

record Comparable : Set₁ where
  field
    A : tp pos
    _≤_ : val A → val A → Set
    _≤ᵇ_ : val A → val A → cmp (F bool)
    ≤ᵇ-reflects-≤ : ∀ {x y b} → ◯ ((x ≤ᵇ y) ≡ ret b → Reflects (x ≤ y) b)
    ≤-refl : Reflexive _≤_
    ≤-trans : Transitive _≤_
    ≤-total : Total _≤_
    ≤-antisym : Antisymmetric _≡_ _≤_
    h-cost : (x y : val A) → ub bool (x ≤ᵇ y) 1

NatComparable : Comparable
NatComparable = record
  { A = U (meta ℕ)
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step' (F bool) 1 (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = reflects
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ → ub/step/suc 0 (ub/ret 0)
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {m n b} → ◯ (step' (F bool) 1 (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step'/ext (F bool) (ret (m ≤ᵇ n)) 1 u) h)
    ... | refl = ≤ᵇ-reflects-≤ m n

module Extras (M : Comparable) where
  open Comparable M

  open import Data.Sum using (inj₁; inj₂)
  open import Data.Empty

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ {x} {y} h with ≤-total x y
  ... | inj₁ h₁ = ⊥-elim (h h₁)
  ... | inj₂ h₂ = h₂
