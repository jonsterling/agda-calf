{-# OPTIONS --without-K #-}

-- The phase distinction for extension.

module Calf.PhaseDistinction where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.CostMonoid

open import Relation.Binary.PropositionalEquality as P


-- Extensional phase.

postulate
  ext : Ω


-- Open/extensional modality.

◯ : □ → □
◯ A = (u : ext) → A

infix 10 ◯⁺_
infix 10 ◯⁻_
postulate
  ext/val : (ext → tp pos) → tp pos
  ext/val/decode : ∀ {A} → val (ext/val A) ≡ ((u : ext) → val (A u))
  {-# REWRITE ext/val/decode #-}

  ext/cmp : (ext → tp neg) → tp neg
  ext/cmp/decode : ∀ {A} → val (U (ext/cmp A)) ≡ ((u : ext) → cmp (A u))
  {-# REWRITE ext/cmp/decode #-}

◯⁺_ : tp pos → tp pos
◯⁺ A = ext/val (λ _ → A)
◯⁻_ : tp neg → tp neg
◯⁻ A = ext/cmp (λ _ → A)


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
                            { isEquivalence = isEquivalence
                            ; ∙-cong = cong₂ _
                            }
                      ; assoc = λ c₁ c₂ c₃ → funext/Ω λ u → +-assoc (c₁ u) (c₂ u) (c₃ u)
                      }
                ; identity =
                    (λ c → funext/Ω λ u → +-identityˡ (c u)) ,
                    (λ c → funext/Ω λ u → +-identityʳ (c u))
                }
          ; isPreorder =
              record
                { isEquivalence = isEquivalence
                ; reflexive = λ { refl u → ≤-refl }
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


-- Closed/intensional modality.

postulate
  ● : tp pos → tp pos
  η : ∀ {A} → val A → val (● A)
  ∗ : ∀ {A} → ext → val (● A)
  η≡∗ : ∀ {A} (a : val A) u → η {A} a ≡ ∗ u
  ●/ind : ∀ {A} (a : val (● A)) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    ((a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    cmp (X a)
  ●/ind/β₁ : ∀ {A} (a : val A) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    (h : (a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    ●/ind (η a) X x0 x1 h ≡ x0 a
  {-# REWRITE ●/ind/β₁ #-}
  ●/ind/β₂ : ∀ {A} (u : ext) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    (h : (a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    ●/ind (∗ u) X x0 x1 h ≡ x1 u
  {-# REWRITE ●/ind/β₂ #-}
