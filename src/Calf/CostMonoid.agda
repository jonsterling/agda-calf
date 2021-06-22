{-# OPTIONS --prop --without-K --rewriting #-}

-- Definition of a cost monoid.

open import Relation.Binary using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)

module Calf.CostMonoid where

open import Level using (Level; 0ℓ; suc; _⊔_)
open import Algebra.Core
open import Relation.Binary.PropositionalEquality using (_≡_)


module _ {ℂ : Set} where
  _≈_ : Rel ℂ 0ℓ
  _≈_ = _≡_

  open import Algebra.Structures _≈_ using (IsCommutativeMonoid)
  open import Relation.Binary.Structures _≈_ using (IsTotalPreorder)

  record IsCostMonoid (_+_ : Op₂ ℂ) (zero : ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
    field
      isCommutativeMonoid : IsCommutativeMonoid _+_ zero
      isTotalPreorder     : IsTotalPreorder _≤_
      +-mono-≤            : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
      z≤c                 : {c : ℂ} → zero ≤ c

    open IsCommutativeMonoid isCommutativeMonoid public
      renaming (comm to +-comm)
      hiding (refl; sym; trans)
    open IsTotalPreorder isTotalPreorder public
      renaming (refl to ≤-refl; trans to ≤-trans)
      hiding (reflexive)

    +-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
    +-monoˡ-≤ n m≤o = +-mono-≤ m≤o (≤-refl {n})

    +-monoʳ-≤ : ∀ n → (n +_) Preserves _≤_ ⟶ _≤_
    +-monoʳ-≤ n m≤o = +-mono-≤ (≤-refl {n}) m≤o

record CostMonoid : Set₁ where
  field
    ℂ            : Set
    _+_          : Op₂ ℂ
    zero         : ℂ
    _≤_          : Rel ℂ 0ℓ
    isCostMonoid : IsCostMonoid _+_ zero _≤_

  open IsCostMonoid isCostMonoid public
