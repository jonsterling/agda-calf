{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayCostMonoid ℓ where

open Agda.Primitive
open import Data.Fin.Base              using (Fin)
open import Data.List.Base             using ([_])
open import Data.Nat.Base              using (ℕ)
open import Data.Product               using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import CalfMonad.CostMonoid
open import CalfMonad.CostMonoids

data ArrayStep : Set (lsuc ℓ) where
  read  : (A : Set ℓ) (n : ℕ) (i : Fin n) (a : A) → ArrayStep
  write : (A : Set ℓ) (n : ℕ) (i : Fin n) (a : A) → ArrayStep
  alloc : (A : Set ℓ) (n : ℕ)                     → ArrayStep

record ArrayCostMonoid ℓ′ : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    costMonoid : CostMonoid ℓ′

  open CostMonoid costMonoid public

  field
    arrayStep : (s : ArrayStep) → ℂ

⊤-ArrayCostMonoid : ∀ ℓ′ → ArrayCostMonoid ℓ′
⊤-ArrayCostMonoid ℓ′ = record
  { costMonoid = ⊤-CostMonoid ℓ′
  ; arrayStep = λ where
    (read  A n i a) → tt
    (write A n i a) → tt
    (alloc A n    ) → tt
  }

ℕ-ArrayCostMonoid : ArrayCostMonoid lzero
ℕ-ArrayCostMonoid = record
  { costMonoid = ℕ-CostMonoid
  ; arrayStep = λ where
    (read  A n i a) → 1
    (write A n i a) → 1
    (alloc A n    ) → 0
  }

List-ArrayCostMonoid : ∀ {ℓ′} (ℂ : Set ℓ′) (arrayStep : (s : ArrayStep) → ℂ) → ArrayCostMonoid ℓ′
List-ArrayCostMonoid ℂ arrayStep = record
  { costMonoid = List-CostMonoid ℂ
  ; arrayStep = λ s → [ arrayStep s ]
  }

ArrayStep-List-ArrayCostMonoid : ArrayCostMonoid (lsuc ℓ)
ArrayStep-List-ArrayCostMonoid = List-ArrayCostMonoid ArrayStep λ s → s

×-ArrayCostMonoid : ∀ {ℓ′ ℓ″} → ArrayCostMonoid ℓ′ → ArrayCostMonoid ℓ″ → ArrayCostMonoid (ℓ′ ⊔ ℓ″)
×-ArrayCostMonoid arrayCostMonoid arrayCostMonoid′ = record
  { costMonoid = ×-CostMonoid costMonoid costMonoid′
  ; arrayStep = λ s → arrayStep s , arrayStep′ s
  }
  where
    open ArrayCostMonoid arrayCostMonoid
    open ArrayCostMonoid arrayCostMonoid′ renaming
      (costMonoid to costMonoid′;
       arrayStep to arrayStep′)

CostGraph-ArrayCostMonoid : ∀ {ℓ′} (ℂ : Set ℓ′) (arrayStep : (s : ArrayStep) → ℂ) → ArrayCostMonoid ℓ′
CostGraph-ArrayCostMonoid ℂ arrayStep = record
  { costMonoid = ParCostMonoid.costMonoid (CostGraph-ParCostMonoid ℂ)
  ; arrayStep = λ s → [ CostGraph.base (arrayStep s) ]
  }

ArrayStep-CostGraph-ArrayCostMonoid : ArrayCostMonoid (lsuc ℓ)
ArrayStep-CostGraph-ArrayCostMonoid = CostGraph-ArrayCostMonoid ArrayStep λ s → s

ℕ²-ArrayCostMonoid : ArrayCostMonoid lzero
ℕ²-ArrayCostMonoid = record
  { costMonoid = ParCostMonoid.costMonoid ℕ²-ParCostMonoid
  ; arrayStep = λ where
    (read  A n i a) → 1 , 1
    (write A n i a) → 1 , 1
    (alloc A n    ) → 0 , 0
  }
