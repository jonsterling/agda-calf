{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)

module Algebra.Cost.Structures (ℂ : Set) where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Algebra.Core
open import Algebra.Definitions {A = ℂ} _≡_
open import Algebra.Structures {A = ℂ} _≡_ public
open import Relation.Binary.Structures {A = ℂ} _≡_
open import Level using (0ℓ)


record IsMonotone (_∙_ : Op₂ ℂ) (_≤_ : Rel ℂ 0ℓ) (isPreorder : IsPreorder _≤_) : Set where
  field
    ∙-mono-≤ : _∙_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

  open IsPreorder isPreorder
    using ()
    renaming (reflexive to ≤-reflexive; refl to ≤-refl; trans to ≤-trans)

  ∙-monoˡ-≤ : ∀ n → (_∙ n) Preserves _≤_ ⟶ _≤_
  ∙-monoˡ-≤ n m≤o = ∙-mono-≤ m≤o (≤-refl {n})

  ∙-monoʳ-≤ : ∀ n → (n ∙_) Preserves _≤_ ⟶ _≤_
  ∙-monoʳ-≤ n m≤o = ∙-mono-≤ (≤-refl {n}) m≤o


record IsCostMonoid (zero : ℂ) (_+_ : Op₂ ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
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


record IsParCostMonoid (𝟘 : ℂ) (_⊕_ : Op₂ ℂ) (_⊗_ : Op₂ ℂ) (_≤_ : Rel ℂ 0ℓ) : Set where
  field
    isMonoid            : IsMonoid _⊕_ 𝟘
    isCommutativeMonoid : IsCommutativeMonoid _⊗_ 𝟘
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
