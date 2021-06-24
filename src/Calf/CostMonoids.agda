{-# OPTIONS --prop --without-K --rewriting --allow-unsolved-metas #-}

-- Common cost monoids.

module Calf.CostMonoids where

open import Calf.CostMonoid
open import Data.Product
open import Relation.Binary.PropositionalEquality

ℕ-CostMonoid : CostMonoid
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isCancellative = record { ∙-cancel-≤ = +-cancel-≤ }
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℕ-Work-ParCostMonoid : ParCostMonoid
ℕ-Work-ParCostMonoid = record
  { ℂ = ℕ
  ; _⊕_ = _+_
  ; 𝟘 = 0
  ; _⊗_ = _+_
  ; 𝟙 = 0
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isCommutativeMonoid = +-0-isCommutativeMonoid
    ; isPreorder = ≤-isPreorder
    ; isCancellative = record { ∙-cancel-≤ = +-cancel-≤ }
    ; isMonotone-⊕ = record { ∙-mono-≤ = +-mono-≤ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℕ-Span-ParCostMonoid : ParCostMonoid
ℕ-Span-ParCostMonoid = record
  { ℂ = ℕ
  ; _⊕_ = _+_
  ; 𝟘 = 0
  ; _⊗_ = _⊔_
  ; 𝟙 = 0
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isCommutativeMonoid = ⊔-0-isCommutativeMonoid
    ; isPreorder = ≤-isPreorder
    ; isCancellative = record { ∙-cancel-≤ = +-cancel-≤ }
    ; isMonotone-⊕ = record { ∙-mono-≤ = +-mono-≤ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = ⊔-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

combineParCostMonoids : ParCostMonoid → ParCostMonoid → ParCostMonoid
combineParCostMonoids pcm₁ pcm₂ = record
  { ℂ = ℂ pcm₁ × ℂ pcm₂
  ; _⊕_ = λ (a₁ , a₂) (b₁ , b₂) → _⊕_ pcm₁ a₁ b₁ , _⊕_ pcm₂ a₂ b₂
  ; 𝟘 = 𝟘 pcm₁ , 𝟘 pcm₂
  ; _⊗_ = λ (a₁ , a₂) (b₁ , b₂) → _⊗_ pcm₁ a₁ b₁ , _⊗_ pcm₂ a₂ b₂
  ; 𝟙 = 𝟙 pcm₁ , 𝟙 pcm₂
  ; _≤_ = λ (a₁ , a₂) (b₁ , b₂) → _≤_ pcm₁ a₁ b₁ × _≤_ pcm₂ a₂ b₂
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = λ h₁ h₂ →
              cong₂ _,_
                (cong₂ (_⊕_ pcm₁) (cong proj₁ h₁) (cong proj₁ h₂))
                (cong₂ (_⊕_ pcm₂) (cong proj₂ h₁) (cong proj₂ h₂))
          }
        ; assoc = λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) → cong₂ _,_ (⊕-assoc pcm₁ a₁ b₁ c₁) (⊕-assoc pcm₂ a₂ b₂ c₂)
        }
      ; identity =
        (λ (a₁ , a₂) → cong₂ _,_ (⊕-identityˡ pcm₁ a₁) (⊕-identityˡ pcm₂ a₂)) ,
        (λ (a₁ , a₂) → cong₂ _,_ (⊕-identityʳ pcm₁ a₁) (⊕-identityʳ pcm₂ a₂))
      }
    ; isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong = λ h₁ h₂ →
                cong₂ _,_
                  (cong₂ (_⊗_ pcm₁) (cong proj₁ h₁) (cong proj₁ h₂))
                  (cong₂ (_⊗_ pcm₂) (cong proj₂ h₁) (cong proj₂ h₂))
            }
          ; assoc = λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) → cong₂ _,_ (⊗-assoc pcm₁ a₁ b₁ c₁) (⊗-assoc pcm₂ a₂ b₂ c₂)
          }
        ; identity =
          (λ (a₁ , a₂) → cong₂ _,_ (⊗-identityˡ pcm₁ a₁) (⊗-identityˡ pcm₂ a₂)) ,
          (λ (a₁ , a₂) → cong₂ _,_ (⊗-identityʳ pcm₁ a₁) (⊗-identityʳ pcm₂ a₂))
        }
      ; comm = λ (a₁ , a₂) (b₁ , b₂) → cong₂ _,_ (⊗-comm pcm₁ a₁ b₁) (⊗-comm pcm₂ a₂ b₂)
      }
    ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ { refl → ≤-refl pcm₁ , ≤-refl pcm₂ }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans pcm₁ h₁ h₁' , ≤-trans pcm₂ h₂ h₂'
      }
    ; isCancellative = record
      { ∙-cancel-≤ =
        (λ (x₁ , x₂) (h₁ , h₂) → ⊕-cancelˡ-≤ pcm₁ x₁ h₁ , ⊕-cancelˡ-≤ pcm₂ x₂ h₂) ,
        (λ (y₁ , y₂) (z₁ , z₂) (h₁ , h₂) → ⊕-cancelʳ-≤ pcm₁ y₁ z₁ h₁ , ⊕-cancelʳ-≤ pcm₂ y₂ z₂ h₂)
      }
    ; isMonotone-⊕ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊕-mono-≤ pcm₁ h₁ h₁' , ⊕-mono-≤ pcm₂ h₂ h₂'
      }
    ; isMonotone-⊗ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊗-mono-≤ pcm₁ h₁ h₁' , ⊗-mono-≤ pcm₂ h₂ h₂'
      }
    }
  }
  where open ParCostMonoid

ℕ²-ParCostMonoid : ParCostMonoid
ℕ²-ParCostMonoid = combineParCostMonoids ℕ-Work-ParCostMonoid ℕ-Span-ParCostMonoid
