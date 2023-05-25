{-# OPTIONS --erased-cubical --prop --rewriting #-}

module Examples.Sequence.CostGraph where

open import Calf.CostMonoid

open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path renaming (_≡_ to _==_)

data CostGraph (A : Set) : Set where
  base : A                         → CostGraph A
  _⊕_  : CostGraph A → CostGraph A → CostGraph A
  𝟘    :                             CostGraph A
  _⊗_  : CostGraph A → CostGraph A → CostGraph A
  𝟙    :                             CostGraph A

  ⊕-assoc     : ∀ x y z → (x ⊕ y) ⊕ z == x ⊕ (y ⊕ z)
  ⊕-identityˡ : ∀ x     →       𝟘 ⊕ x == x
  ⊕-identityʳ : ∀ x     →       x ⊕ 𝟘 == x
  ⊗-assoc     : ∀ x y z → (x ⊗ y) ⊗ z == x ⊗ (y ⊗ z)
  ⊗-identityˡ : ∀ x     →       𝟙 ⊗ x == x
  ⊗-identityʳ : ∀ x     →       x ⊗ 𝟙 == x
  ⊗-comm      : ∀ x y   →       x ⊗ y == y ⊗ x

CostGraph-ParCostMonoid : Set → ParCostMonoid
CostGraph-ParCostMonoid A = record
  { ℂ   = CostGraph A
  ; _⊕_ = _⊕_
  ; 𝟘   = 𝟘
  ; _⊗_ = _⊗_
  ; 𝟙   = 𝟙
  ; _≤_ = _≡_
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = cong₂ _⊕_
          }
        ; assoc = λ x y z → ==⇒≡ (⊕-assoc x y z)
        }
      ; identity = (λ x → ==⇒≡ (⊕-identityˡ x)) , (λ x → ==⇒≡ (⊕-identityʳ x))
      }
    ; isCommutativeMonoid =
      record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = cong₂ _⊗_
              }
            ; assoc = λ x y z → ==⇒≡ (⊗-assoc x y z)
            }
          ; identity = (λ x → ==⇒≡ (⊗-identityˡ x)) , (λ x → ==⇒≡ (⊗-identityʳ x))
          }
        ; comm = λ x y → ==⇒≡ (⊗-comm x y)
        }
    ; isPreorder = isPreorder
    ; isMonotone-⊕ = record { ∙-mono-≤ = cong₂ _⊕_ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = cong₂ _⊗_ }
    }
  }
  where
    ==⇒≡ : ∀ {x y} → x == y → x ≡ y
    ==⇒≡ {x} p = primTransp (λ i → x ≡ p i) i0 refl
