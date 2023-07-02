open import Calf.CostMonoid
open import Data.Nat using (ℕ)

module Examples.Sorting.Comparable
  (costMonoid : CostMonoid) (fromℕ : ℕ → CostMonoid.ℂ costMonoid) where

open CostMonoid costMonoid using (ℂ)

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
    h-cost : (x y : val A) → IsBounded bool (x ≤ᵇ y) (fromℕ 1)

NatComparable : Comparable
NatComparable = record
  { A = nat
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step (F bool) (fromℕ 1) (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = reflects
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ →
      bound/relax
        (λ u → CostMonoid.≤-reflexive costMonoid (CostMonoid.+-identityʳ costMonoid (fromℕ 1)))
        (bound/step (fromℕ 1) (CostMonoid.zero costMonoid) bound/ret)
  }
  where
    open import Calf.Types.Nat

    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {m n b} → ◯ (step (F bool) (fromℕ 1) (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step/ext (F bool) (ret (m ≤ᵇ n)) (fromℕ 1) u) h)
    ... | refl = ≤ᵇ-reflects-≤ m n
