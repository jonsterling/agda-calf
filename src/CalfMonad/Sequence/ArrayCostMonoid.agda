{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayCostMonoid where

open Agda.Primitive
open import Agda.Builtin.List
open import Data.Fin.Base              using (Fin)
open import Data.Nat.Base              using (ℕ)
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Vec.Base              using (Vec)

open import CalfMonad.CostMonoids

data ArrayStep : Set₁ where
  read  : {A : Set} {n : ℕ} (as : Vec A n) (i : Fin n) → ArrayStep
  write : {A : Set} {n : ℕ} (i : Fin n) (a : A)        → ArrayStep
  alloc : (A : Set) (n : ℕ)                            → ArrayStep

record ArrayCostMonoid {ℓ} (ℂ : Set ℓ) : Set (lsuc lzero ⊔ ℓ) where
  field
    arrayStep : ArrayStep → ℂ

open ArrayCostMonoid

⊤-ArrayCostMonoid : ∀ ℓ → ArrayCostMonoid {ℓ} ⊤
⊤-ArrayCostMonoid ℓ .arrayStep _ = _

ℕ-ArrayCostMonoid : ArrayCostMonoid ℕ
ℕ-ArrayCostMonoid .arrayStep (read  as i) = 1
ℕ-ArrayCostMonoid .arrayStep (write i  a) = 1
ℕ-ArrayCostMonoid .arrayStep (alloc A  n) = 0

List-ArrayCostMonoid : ∀ {ℓ} {ℂ : Set ℓ} → (ArrayStep → ℂ) → ArrayCostMonoid (List ℂ)
List-ArrayCostMonoid arrayStep .arrayStep s = arrayStep s ∷ []

×-ArrayCostMonoid : ∀ {ℓ₁ ℓ₂} {ℂ₁ : Set ℓ₁} {ℂ₂ : Set ℓ₂} → ArrayCostMonoid ℂ₁ → ArrayCostMonoid ℂ₂ → ArrayCostMonoid (ℂ₁ × ℂ₂)
×-ArrayCostMonoid arrayCostMonoid₁ arrayCostMonoid₂ .arrayStep s = arrayCostMonoid₁ .arrayStep s , arrayCostMonoid₂ .arrayStep s

CostGraph-ArrayCostMonoid : ∀ {ℓ} {ℂ : Set ℓ} → (ArrayStep → ℂ) → ArrayCostMonoid (CostGraph ℂ)
CostGraph-ArrayCostMonoid arrayStep .arrayStep s = CostGraph.base (arrayStep s) ∷ []

ℕ²-ArrayCostMonoid : ArrayCostMonoid (ℕ × ℕ)
ℕ²-ArrayCostMonoid = ×-ArrayCostMonoid ℕ-ArrayCostMonoid ℕ-ArrayCostMonoid
