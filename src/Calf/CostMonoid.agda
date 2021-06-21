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

  record IsOrderedCommutativeMonoid (_∙_ : Op₂ ℂ) (ε : ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
    field
      isCommutativeMonoid : IsCommutativeMonoid _∙_ ε
      isTotalPreorder     : IsTotalPreorder _≤_
      ∙-mono-≤            : _∙_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

    open IsCommutativeMonoid isCommutativeMonoid public
      using (identityˡ; identityʳ)
      renaming (comm to ∙-comm)
    open IsTotalPreorder isTotalPreorder public
      using ()
      renaming (refl to ≤-refl; trans to ≤-trans)

    ∙-monoˡ-≤ : ∀ n → (_∙ n) Preserves _≤_ ⟶ _≤_
    ∙-monoˡ-≤ n m≤o = ∙-mono-≤ m≤o (≤-refl {n})

    ∙-monoʳ-≤ : ∀ n → (n ∙_) Preserves _≤_ ⟶ _≤_
    ∙-monoʳ-≤ n m≤o = ∙-mono-≤ (≤-refl {n}) m≤o

  record IsCostMonoid (_+_ : Op₂ ℂ) (zero : ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
    field
      isOrderedCommutativeMonoid : IsOrderedCommutativeMonoid _+_ zero _≤_
      z≤c                        : {c : ℂ} → zero ≤ c

    open IsOrderedCommutativeMonoid isOrderedCommutativeMonoid public
      renaming (
        ∙-comm to +-comm;
        ∙-mono-≤ to +-mono-≤;
        ∙-monoˡ-≤ to +-monoˡ-≤;
        ∙-monoʳ-≤ to +-monoʳ-≤
      )

  record IsCancellativeOrderedCommutativeMonoid (_∙_ : Op₂ ℂ) (ε : ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
    field
      isOrderedCommutativeMonoid : IsOrderedCommutativeMonoid _∙_ ε _≤_
      cancel                     : Cancellative _∙_

    open IsOrderedCommutativeMonoid isOrderedCommutativeMonoid public

  record IsParCostMonoid (_⊕_ : Op₂ ℂ) (𝟘 : ℂ) (_⊗_ : Op₂ ℂ) (𝟙 : ℂ) (_≤₊_ : Rel ℂ 0ℓ) (_≤ₓ_ : Rel ℂ 0ℓ) : Set where
    field
      isCostMonoid                           : IsCostMonoid _⊕_ 𝟘 _≤₊_
      isCancellativeOrderedCommutativeMonoid : IsCancellativeOrderedCommutativeMonoid _⊗_ 𝟙 _≤ₓ_

    open IsCostMonoid isCostMonoid public
      renaming (
        identityˡ to ⊕-identityˡ;
        identityʳ to ⊕-identityʳ;
        ≤-refl to ≤₊-refl
      )
    open IsCancellativeOrderedCommutativeMonoid isCancellativeOrderedCommutativeMonoid public
      renaming (
        identityˡ to ⊗-identityˡ;
        identityʳ to ⊗-identityʳ;
        ∙-comm to ⊗-comm;
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
    _⊕_             : Op₂ ℂ
    𝟘               : ℂ
    _⊗_             : Op₂ ℂ
    𝟙               : ℂ
    _≤₊_            : Rel ℂ 0ℓ
    _≤ₓ_            : Rel ℂ 0ℓ
    isParCostMonoid : IsParCostMonoid _⊕_ 𝟘 _⊗_ 𝟙 _≤₊_ _≤ₓ_

  open IsParCostMonoid isParCostMonoid public

  costMonoid : CostMonoid
  costMonoid = record
    { ℂ = ℂ
    ; _+_ = _⊕_
    ; zero = 𝟘
    ; _≤_ = _≤₊_
    ; isCostMonoid = isCostMonoid
    }
