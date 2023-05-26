{-# OPTIONS --erased-cubical --safe #-}

module Calf.CostGraph where

open import Agda.Builtin.Sigma
open import Agda.Primitive.Cubical
open import Algebra.Core
open import Calf.CostMonoid
open import Relation.Binary.PropositionalEquality

module _ (A : Set) where
  data CostGraph : Set

  open import Algebra.Definitions (PathP λ _ → CostGraph)

  data CostGraph where
    base : A → CostGraph
    _⊕_  : Op₂ CostGraph
    𝟘    :     CostGraph
    _⊗_  : Op₂ CostGraph
    𝟙    :     CostGraph

    ⊕-assoc     : Associative     _⊕_
    ⊕-identityˡ : LeftIdentity  𝟘 _⊕_
    ⊕-identityʳ : RightIdentity 𝟘 _⊕_
    ⊗-assoc     : Associative     _⊗_
    ⊗-identityˡ : LeftIdentity  𝟙 _⊗_
    ⊗-identityʳ : RightIdentity 𝟙 _⊗_
    ⊗-comm      : Commutative     _⊗_

CostGraph-ParCostMonoid : Set → ParCostMonoid
CostGraph-ParCostMonoid A = record
  { ℂ = CostGraph A
  ; _⊕_ = _⊕_
  ; 𝟘 = 𝟘
  ; _⊗_ = _⊗_
  ; 𝟙 = 𝟙
  ; _≤_ = _≡_
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = cong₂ _⊕_
          }
        ; assoc = λ x y z → Path⇒≡ (⊕-assoc x y z)
        }
      ; identity = (λ x → Path⇒≡ (⊕-identityˡ x)) , (λ x → Path⇒≡ (⊕-identityʳ x))
      }
    ; isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong = cong₂ _⊗_
            }
          ; assoc = λ x y z → Path⇒≡ (⊗-assoc x y z)
          }
        ; identity = (λ x → Path⇒≡ (⊗-identityˡ x)) , (λ x → Path⇒≡ (⊗-identityʳ x))
        }
      ; comm = λ x y → Path⇒≡ (⊗-comm x y)
      }
    ; isPreorder = isPreorder
    ; isMonotone-⊕ = record { ∙-mono-≤ = cong₂ _⊕_ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = cong₂ _⊗_ }
    }
  }
  where
    Path⇒≡ : ∀ {x y} → PathP _ x y → x ≡ y
    Path⇒≡ {x} p = primTransp (λ i → x ≡ p i) i0 refl
