{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonoids where

open import Data.List.Base                             using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties                       using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Nat.Base                              using (ℕ; _+_; _⊔_)
open import Data.Nat.Properties                        using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Product                               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base                 using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong₂)

open import CalfMonad.CostMonoid

open CostMonoid
open ParCostMonoid

⊤-CostMonoid : ∀ ℓ → CostMonoid {ℓ} ⊤
⊤-CostMonoid ℓ ._⊕_ p q = _
⊤-CostMonoid ℓ .𝟘 = _
⊤-CostMonoid ℓ .⊕-assoc p q r = refl
⊤-CostMonoid ℓ .⊕-identityˡ p = refl
⊤-CostMonoid ℓ .⊕-identityʳ p = refl

⊤-Step : ∀ {ℓ′} (A : Set ℓ′) ℓ → A → ⊤ {ℓ}
⊤-Step A ℓ a = _

ℕ-CostMonoid : CostMonoid ℕ
ℕ-CostMonoid ._⊕_ = _+_
ℕ-CostMonoid .𝟘 = 0
ℕ-CostMonoid .⊕-assoc = +-assoc
ℕ-CostMonoid .⊕-identityˡ = +-identityˡ
ℕ-CostMonoid .⊕-identityʳ = +-identityʳ

List-CostMonoid : ∀ {ℓ} (ℂ : Set ℓ) → CostMonoid (List ℂ)
List-CostMonoid ℂ ._⊕_ = _++_
List-CostMonoid ℂ .𝟘 = []
List-CostMonoid ℂ .⊕-assoc = ++-assoc
List-CostMonoid ℂ .⊕-identityˡ = ++-identityˡ
List-CostMonoid ℂ .⊕-identityʳ = ++-identityʳ

List-Step : ∀ {ℓ′} {A : Set ℓ′} {ℓ} {ℂ : Set ℓ} → (A → ℂ) → A → List ℂ
List-Step step a = [ step a ]

×-CostMonoid : ∀ {ℓ₁ ℓ₂} {ℂ₁ : Set ℓ₁} {ℂ₂ : Set ℓ₂} → CostMonoid ℂ₁ → CostMonoid ℂ₂ → CostMonoid (ℂ₁ × ℂ₂)
×-CostMonoid costMonoid₁ costMonoid₂ ._⊕_ (p₁ , p₂) (q₁ , q₂) = costMonoid₁ ._⊕_ p₁ q₁ , costMonoid₂ ._⊕_ p₂ q₂
×-CostMonoid costMonoid₁ costMonoid₂ .𝟘 = costMonoid₁ .𝟘 , costMonoid₂ .𝟘
×-CostMonoid costMonoid₁ costMonoid₂ .⊕-assoc (p₁ , p₂) (q₁ , q₂) (r₁ , r₂) = cong₂ _,_ (costMonoid₁ .⊕-assoc p₁ q₁ r₁) (costMonoid₂ .⊕-assoc p₂ q₂ r₂)
×-CostMonoid costMonoid₁ costMonoid₂ .⊕-identityˡ (p₁ , p₂) = cong₂ _,_ (costMonoid₁ .⊕-identityˡ p₁) (costMonoid₂ .⊕-identityˡ p₂)
×-CostMonoid costMonoid₁ costMonoid₂ .⊕-identityʳ (p₁ , p₂) = cong₂ _,_ (costMonoid₁ .⊕-identityʳ p₁) (costMonoid₂ .⊕-identityʳ p₂)

×-Step : ∀ {ℓ} {A : Set ℓ} {ℓ₁ ℓ₂} {ℂ₁ : Set ℓ₁} {ℂ₂ : Set ℓ₂} → (A → ℂ₁) → (A → ℂ₂) → A → ℂ₁ × ℂ₂
×-Step step₁ step₂ a = step₁ a , step₂ a

sequentialParCostMonoid : ∀ {ℓ} {ℂ : Set ℓ} → CostMonoid ℂ → ParCostMonoid ℂ
sequentialParCostMonoid costMonoid ._⊗_ = costMonoid ._⊕_

ℕ-ParCostMonoid : ParCostMonoid ℕ
ℕ-ParCostMonoid ._⊗_ = _⊔_

module CostGraph {ℓ} (ℂ : Set ℓ) where
  infixr 6 _⊗ᵍ_
  infixr 5 _∷ᵍ_

  CostGraph : Set ℓ

  data CostGraphBase : Set ℓ where
    base : ℂ → CostGraphBase
    _⊗ᵍ_ : CostGraph → CostGraph → CostGraphBase

  CostGraph = List CostGraphBase

  pattern _∷ᵍ_ p q = base p ∷ q

open CostGraph using (CostGraph; CostGraphBase; _∷ᵍ_; _⊗ᵍ_) public

CostGraph-CostMonoid : ∀ {ℓ} (ℂ : Set ℓ) → CostMonoid (CostGraph ℂ)
CostGraph-CostMonoid ℂ = List-CostMonoid (CostGraphBase ℂ)

CostGraph-ParCostMonoid : ∀ {ℓ} (ℂ : Set ℓ) → ParCostMonoid (CostGraph ℂ)
CostGraph-ParCostMonoid ℂ ._⊗_ p q = [ p ⊗ᵍ q ]

CostGraph-Step : ∀ {ℓ′} {A : Set ℓ′} {ℓ} {ℂ : Set ℓ} → (A → ℂ) → A → CostGraph ℂ
CostGraph-Step step a = step a ∷ᵍ []

×-ParCostMonoid : ∀ {ℓ₁ ℓ₂} {ℂ₁ : Set ℓ₁} {ℂ₂ : Set ℓ₂} → ParCostMonoid ℂ₁ → ParCostMonoid ℂ₂ → ParCostMonoid (ℂ₁ × ℂ₂)
×-ParCostMonoid costMonoid₁ costMonoid₂ ._⊗_ (p₁ , p₂) (q₁ , q₂) = costMonoid₁ ._⊗_ p₁ q₁ , costMonoid₂ ._⊗_ p₂ q₂

ℕ²-ParCostMonoid : ParCostMonoid (ℕ × ℕ)
ℕ²-ParCostMonoid = ×-ParCostMonoid (sequentialParCostMonoid ℕ-CostMonoid) ℕ-ParCostMonoid
