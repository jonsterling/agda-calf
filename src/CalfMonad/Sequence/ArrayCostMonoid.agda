{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.Sequence.ArrayCostMonoid {M : Set → Set} (monad : Monad M) where

open Agda.Primitive
open import Data.List.Base             using (List; [_])
open import Data.Nat.Base              using (ℕ)
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Types.Fin monad
open import CalfMonad.CBPV.Types.Nat monad
open import CalfMonad.CBPV.Types.Vec monad
open import CalfMonad.CostMonoids

data ArrayStep : Set₁ where
  read  : {A : tp+} {n : val nat} (as : val (vec A n)) (i : val (fin n)) → ArrayStep
  write : {A : tp+} {n : val nat} (i : val (fin n)) (a : val A)          → ArrayStep
  alloc : (A : tp+) (n : val nat)                                        → ArrayStep

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
List-ArrayCostMonoid arrayStep .arrayStep s = [ arrayStep s ]

×-ArrayCostMonoid : ∀ {ℓ₁ ℓ₂} {ℂ₁ : Set ℓ₁} {ℂ₂ : Set ℓ₂} → ArrayCostMonoid ℂ₁ → ArrayCostMonoid ℂ₂ → ArrayCostMonoid (ℂ₁ × ℂ₂)
×-ArrayCostMonoid arrayCostMonoid₁ arrayCostMonoid₂ .arrayStep s = arrayCostMonoid₁ .arrayStep s , arrayCostMonoid₂ .arrayStep s

CostGraph-ArrayCostMonoid : ∀ {ℓ} {ℂ : Set ℓ} → (ArrayStep → ℂ) → ArrayCostMonoid (CostGraph ℂ)
CostGraph-ArrayCostMonoid arrayStep .arrayStep s = [ CostGraph.base (arrayStep s) ]

ℕ²-ArrayCostMonoid : ArrayCostMonoid (ℕ × ℕ)
ℕ²-ArrayCostMonoid = ×-ArrayCostMonoid ℕ-ArrayCostMonoid ℕ-ArrayCostMonoid
