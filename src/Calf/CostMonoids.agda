{-# OPTIONS --prop --without-K --rewriting #-}

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
    { isOrderedCommutativeMonoid = record
      { isCommutativeMonoid = +-0-isCommutativeMonoid
      ; isTotalPreorder = ≤-isTotalPreorder
      ; ∙-mono-≤ = +-mono-≤
      }
    ; z≤c = z≤n
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality

ℕ²-ParCostMonoid : ParCostMonoid
ℕ²-ParCostMonoid = record
  { ℂ = ℕ × ℕ
  ; _+_ = λ (w₁ , s₁) (w₂ , s₂) → (w₁ + w₂) , (s₁ + s₂)
  ; zero = zero , zero
  ; _⊗_ = λ (w₁ , s₁) (w₂ , s₂) → (w₁ + w₂) , (s₁ ⊔ s₂)
  ; one = zero , zero
  ; _≤₊_ = λ (w₁ , _) (w₂ , _) → w₁ ≤ w₂
  ; _≤ₓ_ = λ (_ , s₁) (_ , s₂) → s₁ ≤ s₂
  ; isParCostMonoid = record
      { isCostMonoid = record
        { isOrderedCommutativeMonoid = record
          { isCommutativeMonoid = record
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
            ; comm = λ (w₁ , s₁) (w₂ , s₂) → cong₂ _,_ (+-comm w₁ w₂) (+-comm s₁ s₂) 
            }
          ; isTotalPreorder = record
            { isPreorder = record
              { isEquivalence = isEquivalence
              ; reflexive = λ { refl → ≤-refl }
              ; trans = ≤-trans
              }
            ; total = λ (w₁ , _) (w₂ , _) → ≤-total w₁ w₂
            }
          ; ∙-mono-≤ = +-mono-≤
          }
        ; z≤c = z≤n
        }
      ; isCancellativeOrderedCommutativeMonoid = record
        { isOrderedCommutativeMonoid = record
          { isCommutativeMonoid = record
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
          ; isTotalPreorder = record
            { isPreorder = record
              { isEquivalence = isEquivalence
              ; reflexive = λ { refl → ≤-refl }
              ; trans = ≤-trans
              }
            ; total = λ (_ , s₁) (_ , s₂) → ≤-total s₁ s₂
            }
          ; ∙-mono-≤ = ⊔-mono-≤
          }
        ; cancel =
            (λ (w , s) h → cong₂ _,_ (+-cancelˡ-≡ w (cong proj₁ h)) {!  !}) ,
            (λ (w₁ , s₁) (w₂ , s₂) h → cong₂ _,_ (+-cancelʳ-≡ w₁ w₂ (cong proj₁ h)) {!   !})
        }
      }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality
