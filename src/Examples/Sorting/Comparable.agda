{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid
open import Data.Nat using (ℕ)

module Examples.Sorting.Comparable
  (costMonoid : CostMonoid) (fromℕ : ℕ → CostMonoid.ℂ costMonoid) where

open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.Bounded costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Reflects
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum
open import Function


record Comparable : Set₁ where
  field
    A : tp pos
    _≤_ : val A → val A → Set
    _≤ᵇ_ : val A → val A → cmp (F bool)
    ≤ᵇ-reflects-≤ : ∀ {x y b} → ◯ ((x ≤ᵇ y) ≡ ret b ⇔ Reflects (x ≤ y) b)
    ≤-refl : Reflexive _≤_
    ≤-trans : Transitive _≤_
    ≤-total : Total _≤_
    _≤?_ : Decidable _≤_
    ≤-antisym : Antisymmetric _≡_ _≤_
    h-cost : (x y : val A) → IsBounded bool (x ≤ᵇ y) (fromℕ 1)

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ ¬x≤y with ≤-total _ _
  ... | inj₁ x≤y = contradiction x≤y ¬x≤y
  ... | inj₂ y≤x = y≤x

NatComparable : Comparable
NatComparable = record
  { A = nat
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step (F bool) (fromℕ 1) (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = λ u → record
      { f = reflects u
      ; g = reflects⁻¹ u
      ; cong₁ = Eq.cong (reflects u)
      ; cong₂ = Eq.cong (reflects⁻¹ u)
      }
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; _≤?_ = _≤?_
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ _ → ≲-refl
  }
  where
    open import Calf.Types.Nat

    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {x y b} → ◯ (step (F bool) (fromℕ 1) (ret (x ≤ᵇ y)) ≡ ret {bool} b → Reflects (x ≤ y) b)
    reflects {x} {y} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step/ext (F bool) (ret (x ≤ᵇ y)) (fromℕ 1) u) h)
    ... | refl = ≤ᵇ-reflects-≤ x y

    reflects⁻¹ : ∀ {x y b} → ◯ (Reflects (x ≤ y) b → step (F (U (meta Bool))) (fromℕ 1) (ret (x ≤ᵇ y)) ≡ ret b)
    reflects⁻¹ {x} {y} u h with x ≤ᵇ y | invert (≤ᵇ-reflects-≤ x y)
    reflects⁻¹ {x} {y} u (ofʸ x≤y)  | false | ¬x≤y = contradiction x≤y ¬x≤y
    reflects⁻¹ {x} {y} u (ofⁿ ¬x≤y) | false | _    = step/ext (F bool) (ret false) (fromℕ 1) u
    reflects⁻¹ {x} {y} u (ofʸ x≤y)  | true  | _    = step/ext (F bool) (ret true) (fromℕ 1) u
    reflects⁻¹ {x} {y} u (ofⁿ ¬x≤y) | true  | x≤y  = contradiction x≤y ¬x≤y
