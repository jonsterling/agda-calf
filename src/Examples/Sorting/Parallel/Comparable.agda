{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Parallel.Comparable where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid
  renaming (
    _≤_ to _≤ₚ_;
    ≤-refl to ≤ₚ-refl;
    ≤-trans to ≤ₚ-trans;
    module ≤-Reasoning to ≤ₚ-Reasoning
  ) public

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.Bounded costMonoid

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
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
    h-cost : (x y : val A) → IsBounded bool (x ≤ᵇ y) (1 , 1)

NatComparable : Comparable
NatComparable = record
  { A = nat
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step (F bool) (1 , 1) (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = reflects
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ → bound/step (1 , 1) 𝟘 bound/ret
  }
  where
    open import Calf.Types.Nat

    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {m n b} → ◯ (step (F bool) (1 , 1) (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step/ext (F bool) (ret (m ≤ᵇ n)) (1 , 1) u) h)
    ... | refl = ≤ᵇ-reflects-≤ m n
