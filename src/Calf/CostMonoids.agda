{-# OPTIONS --prop --without-K --rewriting --allow-unsolved-metas #-}

-- Common cost monoids.

module Calf.CostMonoids where

open import Calf.CostMonoid
open import Data.Product

ℕ-CostMonoid : CostMonoid
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality

ℕ²-ParCostMonoid : ParCostMonoid
ℕ²-ParCostMonoid = record
  { ℂ = ℕ × ℕ
  ; _⊕_ = λ (w₁ , s₁) (w₂ , s₂) → (w₁ + w₂) , (s₁ + s₂)
  ; 𝟘 = zero , zero
  ; _⊗_ = λ (w₁ , s₁) (w₂ , s₂) → (w₁ + w₂) , (s₁ ⊔ s₂)
  ; 𝟙 = zero , zero
  ; _≤_ = λ (w₁ , s₁) (w₂ , s₂) → w₁ ≤ w₂ × s₁ ≤ s₂
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = λ h₁ h₂ →
              cong₂ _,_
                (cong₂ _+_ (cong proj₁ h₁) (cong proj₁ h₂))
                (cong₂ _+_ (cong proj₂ h₁) (cong proj₂ h₂))
          }
        ; assoc = λ (w₁ , s₁) (w₂ , s₂) (w₃ , s₃) → cong₂ _,_ (+-assoc w₁ w₂ w₃) (+-assoc s₁ s₂ s₃)
        }
      ; identity =
        (λ (w , s) → cong₂ _,_ (+-identityˡ w) (+-identityˡ s)) ,
        (λ (w , s) → cong₂ _,_ (+-identityʳ w) (+-identityʳ s))
      }
    ; isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong = λ h₁ h₂ →
                cong₂ _,_
                  (cong₂ _+_ (cong proj₁ h₁) (cong proj₁ h₂))
                  (cong₂ _⊔_ (cong proj₂ h₁) (cong proj₂ h₂))
            }
          ; assoc = λ (w₁ , s₁) (w₂ , s₂) (w₃ , s₃) → cong₂ _,_ (+-assoc w₁ w₂ w₃) (⊔-assoc s₁ s₂ s₃)
          }
        ; identity =
            (λ (w , s) → cong₂ _,_ (+-identityˡ w) (⊔-identityˡ s)) ,
            (λ (w , s) → cong₂ _,_ (+-identityʳ w) (⊔-identityʳ s))
        }
      ; comm = λ (w₁ , s₁) (w₂ , s₂) → cong₂ _,_ (+-comm w₁ w₂) (⊔-comm s₁ s₂)
      }
    ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ { refl → ≤-refl , ≤-refl }
      ; trans = λ (hw₁ , hs₁) (hw₂ , hs₂) → ≤-trans hw₁ hw₂ , ≤-trans hs₁ hs₂
      }
    ; isMonotone-⊕ = record
      { ∙-mono-≤ = λ (hw₁ , hs₁) (hw₂ , hs₂) → (+-mono-≤ hw₁ hw₂) , (+-mono-≤ hs₁ hs₂)
      }
    ; isMonotone-⊗ = record
      { ∙-mono-≤ = λ (hw₁ , hs₁) (hw₂ , hs₂) → (+-mono-≤ hw₁ hw₂) , (⊔-mono-≤ hs₁ hs₂)
      }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality
