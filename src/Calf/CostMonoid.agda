{-# OPTIONS --prop --without-K --rewriting #-}

-- Definition of a cost monoid.

open import Relation.Binary using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)

module Calf.CostMonoid where

open import Level using (Level; 0ℓ; suc; _⊔_)
open import Algebra.Core
open import Relation.Binary.PropositionalEquality using (_≡_; resp₂)
open import Data.Product

module _ {ℂ : Set} where
  Relation = Rel ℂ 0ℓ

  private
    _≈_ : Relation
    _≈_ = _≡_

  open import Algebra.Definitions _≈_
  open import Algebra.Structures _≈_ public
  open import Relation.Binary.Structures _≈_

  record IsCancellative (_∙_ : Op₂ ℂ) : Set where
    field
      ∙-cancel-≡ : Cancellative _∙_

    ∙-cancelˡ-≡ : LeftCancellative _∙_
    ∙-cancelˡ-≡ = proj₁ ∙-cancel-≡

    ∙-cancelʳ-≡ : RightCancellative _∙_
    ∙-cancelʳ-≡ = proj₂ ∙-cancel-≡

  record IsMonotone (_∙_ : Op₂ ℂ) (_≤_ : Relation) (isPreorder : IsPreorder _≤_) : Set where
    field
      ∙-mono-≤ : _∙_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

    open IsPreorder isPreorder
      using ()
      renaming (reflexive to ≤-reflexive; refl to ≤-refl; trans to ≤-trans)

    ∙-monoˡ-≤ : ∀ n → (_∙ n) Preserves _≤_ ⟶ _≤_
    ∙-monoˡ-≤ n m≤o = ∙-mono-≤ m≤o (≤-refl {n})

    ∙-monoʳ-≤ : ∀ n → (n ∙_) Preserves _≤_ ⟶ _≤_
    ∙-monoʳ-≤ n m≤o = ∙-mono-≤ (≤-refl {n}) m≤o

  record IsCostMonoid (_+_ : Op₂ ℂ) (zero : ℂ) (_≤_ : Relation) : Set where
    field
      isMonoid       : IsMonoid _+_ zero
      isPreorder     : IsPreorder _≤_
      isMonotone     : IsMonotone _+_ _≤_ isPreorder

    open IsMonoid isMonoid public
      using ()
      renaming (
        identityˡ to +-identityˡ;
        identityʳ to +-identityʳ;
        assoc to +-assoc
      )

    open IsPreorder isPreorder public
      using ()
      renaming (reflexive to ≤-reflexive; refl to ≤-refl; trans to ≤-trans)

    open IsMonotone isMonotone public
      renaming (
        ∙-mono-≤ to +-mono-≤;
        ∙-monoˡ-≤ to +-monoˡ-≤;
        ∙-monoʳ-≤ to +-monoʳ-≤
      )

  record IsParCostMonoid (_⊕_ : Op₂ ℂ) (𝟘 : ℂ) (_⊗_ : Op₂ ℂ) (𝟙 : ℂ) (_≤_ : Relation) : Set where
    field
      isMonoid            : IsMonoid _⊕_ 𝟘
      isCommutativeMonoid : IsCommutativeMonoid _⊗_ 𝟙
      isPreorder          : IsPreorder _≤_
      isMonotone-⊕        : IsMonotone _⊕_ _≤_ isPreorder
      isMonotone-⊗        : IsMonotone _⊗_ _≤_ isPreorder

    open IsMonoid isMonoid public
      using ()
      renaming (
        identityˡ to ⊕-identityˡ;
        identityʳ to ⊕-identityʳ;
        assoc to ⊕-assoc
      )

    open IsCommutativeMonoid isCommutativeMonoid public
      using ()
      renaming (
        identityˡ to ⊗-identityˡ;
        identityʳ to ⊗-identityʳ;
        assoc to ⊗-assoc;
        comm to ⊗-comm
      )

    open IsPreorder isPreorder public
      using ()
      renaming (reflexive to ≤-reflexive; refl to ≤-refl; trans to ≤-trans)

    open IsMonotone isMonotone-⊕ public
      renaming (
        ∙-mono-≤ to ⊕-mono-≤;
        ∙-monoˡ-≤ to ⊕-monoˡ-≤;
        ∙-monoʳ-≤ to ⊕-monoʳ-≤
      )

    open IsMonotone isMonotone-⊗ public
      renaming (
        ∙-mono-≤ to ⊗-mono-≤;
        ∙-monoˡ-≤ to ⊗-monoˡ-≤;
        ∙-monoʳ-≤ to ⊗-monoʳ-≤
      )

record CostMonoid : Set₁ where
  infixl 6 _+_

  field
    ℂ            : Set
    _+_          : Op₂ ℂ
    zero         : ℂ
    _≤_          : Relation
    isCostMonoid : IsCostMonoid _+_ zero _≤_

  open IsCostMonoid isCostMonoid public

  module ≤-Reasoning where
    open import Relation.Binary.Reasoning.Base.Triple
      isPreorder
      ≤-trans
      (resp₂ _≤_)
      (λ h → h)
      ≤-trans
      ≤-trans
      public
      hiding (step-≈; step-≈˘; step-<)

record ParCostMonoid : Set₁ where
  infixl 7 _⊗_
  infixl 6 _⊕_

  field
    ℂ               : Set
    _⊕_             : Op₂ ℂ
    𝟘               : ℂ
    _⊗_             : Op₂ ℂ
    𝟙               : ℂ
    _≤_             : Relation
    isParCostMonoid : IsParCostMonoid _⊕_ 𝟘 _⊗_ 𝟙 _≤_

  open IsParCostMonoid isParCostMonoid public

  costMonoid : CostMonoid
  costMonoid = record
    { ℂ = ℂ
    ; _+_ = _⊕_
    ; zero = 𝟘
    ; _≤_ = _≤_
    ; isCostMonoid = record
      { isMonoid = isMonoid
      ; isPreorder = isPreorder
      ; isMonotone = isMonotone-⊕
      }
    }

  module ≤-Reasoning where
    open import Relation.Binary.Reasoning.Base.Triple
      isPreorder
      ≤-trans
      (resp₂ _≤_)
      (λ h → h)
      ≤-trans
      ≤-trans
      public
      hiding (step-≈; step-≈˘; step-<)
