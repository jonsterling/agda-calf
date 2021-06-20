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

  open import Algebra.Definitions _≈_
  open import Algebra.Structures _≈_
  open import Relation.Binary.Structures _≈_

  record IsCostMonoid (_+_ : Op₂ ℂ) (zero : ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
    field
      isCommutativeMonoid : IsCommutativeMonoid _+_ zero
      isTotalPreorder     : IsTotalPreorder _≤_
      +-mono-≤            : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
      z≤c                 : {c : ℂ} → zero ≤ c

    open IsCommutativeMonoid isCommutativeMonoid public
      using (identityˡ; identityʳ)
      renaming (comm to +-comm)
    open IsTotalPreorder isTotalPreorder public
      using ()
      renaming (refl to ≤-refl; trans to ≤-trans)

    +-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
    +-monoˡ-≤ n m≤o = +-mono-≤ m≤o (≤-refl {n})

    +-monoʳ-≤ : ∀ n → (n +_) Preserves _≤_ ⟶ _≤_
    +-monoʳ-≤ n m≤o = +-mono-≤ (≤-refl {n}) m≤o

  record IsOrderedCancellativeCommutativeMonoid (_*_ : Op₂ ℂ) (one : ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
    field
      isCommutativeMonoid : IsCommutativeMonoid _*_ one
      isTotalPreorder     : IsTotalPreorder _≤_
      cancel              : Cancellative _*_

    open IsCommutativeMonoid isCommutativeMonoid public
      using (identityˡ; identityʳ)
      renaming (comm to *-comm)
    open IsTotalPreorder isTotalPreorder public
      using ()
      renaming (refl to ≤-refl; trans to ≤-trans)

  record IsParCostMonoid (_+_ : Op₂ ℂ) (zero : ℂ) (_⊗_ : Op₂ ℂ) (one : ℂ) (_≤₊_ : Rel ℂ 0ℓ) (_≤ₓ_ : Rel ℂ 0ℓ) : Set where
    field
      isCostMonoid                           : IsCostMonoid _+_ zero _≤₊_
      isOrderedCancellativeCommutativeMonoid : IsOrderedCancellativeCommutativeMonoid _⊗_ one _≤ₓ_

    open IsCostMonoid isCostMonoid public
      renaming (
        identityˡ to +-identityˡ;
        identityʳ to +-identityʳ;
        ≤-refl to ≤₊-refl
      )
    open IsOrderedCancellativeCommutativeMonoid isOrderedCancellativeCommutativeMonoid public
      renaming (
        identityˡ to *-identityˡ;
        identityʳ to *-identityʳ;
        *-comm to ⊗-comm;
        ≤-refl to ≤ₓ-refl
      )

record CostMonoid : Set₁ where
  field
    ℂ            : Set
    _+_          : Op₂ ℂ
    zero         : ℂ
    _≤_          : Rel ℂ 0ℓ
    isCostMonoid : IsCostMonoid _+_ zero _≤_

  open IsCostMonoid isCostMonoid public

record ParCostMonoid : Set₁ where
  field
    ℂ               : Set
    _+_             : Op₂ ℂ
    zero            : ℂ
    _⊗_             : Op₂ ℂ
    one             : ℂ
    _≤₊_            : Rel ℂ 0ℓ
    _≤ₓ_            : Rel ℂ 0ℓ
    isParCostMonoid : IsParCostMonoid _+_ zero _⊗_ one _≤₊_ _≤ₓ_

  open IsParCostMonoid isParCostMonoid public

  costMonoid : CostMonoid
  costMonoid = record
    { ℂ = ℂ
    ; _+_ = _+_
    ; zero = zero
    ; _≤_ = _≤₊_
    ; isCostMonoid = isCostMonoid
    }
