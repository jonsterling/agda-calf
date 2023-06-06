{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayCostMonoid ℓ where

open Agda.Primitive
open import Data.Fin.Base              using (Fin)
open import Data.List.Base             using (List; [_])
open import Data.Nat.Base              using (ℕ)
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Vec.Base              using (Vec)

open import CalfMonad.CostMonoids

data ArrayStep : Set (lsuc ℓ) where
  read  : (A : Set ℓ) (n : ℕ) (as : Vec A n) (i : Fin n) → ArrayStep
  write : (A : Set ℓ) (n : ℕ) (i : Fin n)    (a : A)     → ArrayStep
  alloc : (A : Set ℓ) (n : ℕ)                            → ArrayStep

record ArrayCostMonoid {ℓ′} (ℂ : Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′) where
  field
    arrayStep : ArrayStep → ℂ

open ArrayCostMonoid

⊤-ArrayCostMonoid : ∀ ℓ′ → ArrayCostMonoid {ℓ′} ⊤
⊤-ArrayCostMonoid ℓ′ .arrayStep _ = tt

ℕ-ArrayCostMonoid : ArrayCostMonoid ℕ
ℕ-ArrayCostMonoid .arrayStep (read  A n as i) = 1
ℕ-ArrayCostMonoid .arrayStep (write A n i  a) = 1
ℕ-ArrayCostMonoid .arrayStep (alloc A n     ) = 0

List-ArrayCostMonoid : ∀ {ℓ′} {ℂ : Set ℓ′} → (ArrayStep → ℂ) → ArrayCostMonoid (List ℂ)
List-ArrayCostMonoid arrayStep .arrayStep s = [ arrayStep s ]

ArrayStep-List-ArrayCostMonoid : ArrayCostMonoid (List ArrayStep)
ArrayStep-List-ArrayCostMonoid = List-ArrayCostMonoid λ s → s

×-ArrayCostMonoid : ∀ {ℓ₁ ℓ₂} {ℂ₁ : Set ℓ₁} {ℂ₂ : Set ℓ₂} → ArrayCostMonoid ℂ₁ → ArrayCostMonoid ℂ₂ → ArrayCostMonoid (ℂ₁ × ℂ₂)
×-ArrayCostMonoid arrayCostMonoid₁ arrayCostMonoid₂ .arrayStep s = arrayCostMonoid₁ .arrayStep s , arrayCostMonoid₂ .arrayStep s

CostGraph-ArrayCostMonoid : ∀ {ℓ′} {ℂ : Set ℓ′} → (ArrayStep → ℂ) → ArrayCostMonoid (CostGraph ℂ)
CostGraph-ArrayCostMonoid arrayStep .arrayStep s = [ CostGraph.base (arrayStep s) ]

ArrayStep-CostGraph-ArrayCostMonoid : ArrayCostMonoid (CostGraph ArrayStep)
ArrayStep-CostGraph-ArrayCostMonoid = CostGraph-ArrayCostMonoid λ s → s

ℕ²-ArrayCostMonoid : ArrayCostMonoid (ℕ × ℕ)
ℕ²-ArrayCostMonoid = ×-ArrayCostMonoid ℕ-ArrayCostMonoid ℕ-ArrayCostMonoid
