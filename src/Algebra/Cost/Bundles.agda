{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Cost.Bundles where

open import Algebra.Core
open import Algebra.Cost.Structures
open import Relation.Binary using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; resp₂)
open import Level using (0ℓ)


record CostMonoid : Set₁ where
  infixl 6 _+_

  field
    ℂ            : Set
    zero         : ℂ
    _+_          : Op₂ ℂ
    _≤_          : Rel ℂ 0ℓ
    isCostMonoid : IsCostMonoid ℂ zero _+_ _≤_

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
    𝟘               : ℂ
    _⊕_             : Op₂ ℂ
    _⊗_             : Op₂ ℂ
    _≤_             : Rel ℂ 0ℓ
    isParCostMonoid : IsParCostMonoid ℂ 𝟘 _⊕_ _⊗_ _≤_

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
