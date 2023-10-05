{-# OPTIONS --rewriting #-}

-- Open/extensional modality.

module Calf.Phase.Open where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Calf.Phase.Core


◯ : □ → □
◯ 𝕁 = (u : ext) → 𝕁

postulate
  open⁺ : (ext → tp⁺) → tp⁺
  open⁺/decode : ∀ {A} → val (open⁺ A) ≡ ((u : ext) → val (A u))
  {-# REWRITE open⁺/decode #-}

  open⁻ : (ext → tp⁻) → tp⁻
  open⁻/decode : ∀ {A} → val (U (open⁻ A)) ≡ ((u : ext) → cmp (A u))
  {-# REWRITE open⁻/decode #-}

infix 10 ◯⁺_ ◯⁻_
◯⁺_ : tp⁺ → tp⁺
◯⁺ A = open⁺ λ _ → A
◯⁻_ : tp⁻ → tp⁻
◯⁻ A = open⁻ λ _ → A


module _ where
  open import Algebra.Cost

  ◯-CostMonoid : CostMonoid → CostMonoid
  ◯-CostMonoid cm =
    record
      { ℂ = ◯ ℂ
      ; _+_ = λ c₁ c₂ u → c₁ u + c₂ u
      ; zero = λ u → zero
      ; _≤_ = λ c₁ c₂ → (u : ext) → c₁ u ≤ c₂ u
      ; isCostMonoid =
          record
            { isMonoid =
                record
                  { isSemigroup =
                      record
                        { isMagma =
                            record
                              { isEquivalence = Eq.isEquivalence
                              ; ∙-cong = Eq.cong₂ _
                              }
                        ; assoc = λ c₁ c₂ c₃ → funext/Ω λ u → +-assoc (c₁ u) (c₂ u) (c₃ u)
                        }
                  ; identity =
                      (λ c → funext/Ω λ u → +-identityˡ (c u)) ,
                      (λ c → funext/Ω λ u → +-identityʳ (c u))
                  }
            ; isPreorder =
                record
                  { isEquivalence = Eq.isEquivalence
                  ; reflexive = λ h u → ≤-reflexive (Eq.cong (λ x → x u) h)
                  ; trans = λ h₁ h₂ u → ≤-trans (h₁ u) (h₂ u)
                  }
            ; isMonotone =
                record
                  { ∙-mono-≤ = λ h₁ h₂ u → +-mono-≤ (h₁ u) (h₂ u)
                  }
            }
      }
      where
        open CostMonoid cm
        open import Data.Product
