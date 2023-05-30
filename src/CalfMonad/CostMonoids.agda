{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonoids where

open import Data.List.Base             using (List; []; [_]; _++_)
open import Data.List.Properties       using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Nat.Base              using (ℕ; _+_; _⊔_)
open import Data.Nat.Properties        using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong₂)

open import CalfMonad.CostMonoid

⊤-CostMonoid : ∀ ℓ → CostMonoid ℓ
⊤-CostMonoid ℓ = record
  { ℂ = ⊤
  ; _⊕_ = λ p q → tt
  ; 𝟘 = tt
  ; ⊕-assoc = λ p q r → refl
  ; ⊕-identityˡ = λ p → refl
  ; ⊕-identityʳ = λ p → refl
  }

ℕ-CostMonoid : CostMonoid _
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; _⊕_ = _+_
  ; 𝟘 = 0
  ; ⊕-assoc = +-assoc
  ; ⊕-identityˡ = +-identityˡ
  ; ⊕-identityʳ = +-identityʳ
  }

List-CostMonoid : ∀ {ℓ} → Set ℓ → CostMonoid ℓ
List-CostMonoid ℂ = record
  { ℂ = List ℂ
  ; _⊕_ = _++_
  ; 𝟘 = []
  ; ⊕-assoc = ++-assoc
  ; ⊕-identityˡ = ++-identityˡ
  ; ⊕-identityʳ = ++-identityʳ
  }

×-CostMonoid : ∀ {ℓ ℓ′} → CostMonoid ℓ → CostMonoid ℓ′ → CostMonoid _
×-CostMonoid costMonoid costMonoid′ = record
  { ℂ = ℂ × ℂ′
  ; _⊕_ = λ (p , p′) (q , q′) → p ⊕ q , p′ ⊕′ q′
  ; 𝟘 = (𝟘 , 𝟘′)
  ; ⊕-assoc = λ (p , p′) (q , q′) (r , r′) → cong₂ _,_ (⊕-assoc p q r) (⊕-assoc′ p′ q′ r′)
  ; ⊕-identityˡ = λ (p , p′) → cong₂ _,_ (⊕-identityˡ p) (⊕-identityˡ′ p′)
  ; ⊕-identityʳ = λ (p , p′) → cong₂ _,_ (⊕-identityʳ p) (⊕-identityʳ′ p′)
  }
  where
    open CostMonoid costMonoid
    open CostMonoid costMonoid′ renaming
      (ℂ to ℂ′; _⊕_ to _⊕′_; 𝟘 to 𝟘′;
       ⊕-assoc to ⊕-assoc′;
       ⊕-identityˡ to ⊕-identityˡ′;
       ⊕-identityʳ to ⊕-identityʳ′)

sequentialParCostMonoid : ∀ {ℓ} → CostMonoid ℓ → ParCostMonoid ℓ
sequentialParCostMonoid costMonoid = record
  { costMonoid = costMonoid
  ; _⊗_ = _⊕_
  }
  where
    open CostMonoid costMonoid

ℕ-ParCostMonoid : ParCostMonoid _
ℕ-ParCostMonoid = record
  { costMonoid = ℕ-CostMonoid
  ; _⊗_ = _⊔_
  }

module CostGraph {ℓ} (ℂ : Set ℓ) where
  CostGraph : Set ℓ

  data CostGraphBase : Set ℓ where
    base : ℂ → CostGraphBase
    _⊗_ : CostGraph → CostGraph → CostGraphBase

  CostGraph = List CostGraphBase

CostGraph-ParCostMonoid : ∀ {ℓ} → Set ℓ → ParCostMonoid ℓ
CostGraph-ParCostMonoid ℂ = record
  { costMonoid = record (List-CostMonoid CostGraphBase) { ℂ = CostGraph }
  ; _⊗_ = λ p q → [ p ⊗ q ]
  }
  where
    open CostGraph ℂ

×-ParCostMonoid : ∀ {ℓ ℓ′} → ParCostMonoid ℓ → ParCostMonoid ℓ′ → ParCostMonoid _
×-ParCostMonoid parCostMonoid parCostMonoid′ = record
  { costMonoid = ×-CostMonoid costMonoid costMonoid′
  ; _⊗_ = λ (p , p′) (q , q′) → p ⊗ q , p′ ⊗′ q′
  }
  where
    open ParCostMonoid parCostMonoid
    open ParCostMonoid parCostMonoid′ renaming
      (costMonoid to costMonoid′;
       _⊗_ to _⊗′_)

ℕ²-ParCostMonoid : ParCostMonoid _
ℕ²-ParCostMonoid = ×-ParCostMonoid (sequentialParCostMonoid ℕ-CostMonoid) ℕ-ParCostMonoid
