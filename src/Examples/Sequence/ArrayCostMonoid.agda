{-# OPTIONS --cubical-compatible --prop --rewriting #-}

module Examples.Sequence.ArrayCostMonoid where

open import Calf.CostMonoid
open import Calf.CostMonoids
open import Calf.Metalanguage

open import Data.Fin     using (Fin)
open import Data.List    using ([_])
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_)

data ArrayStep : Set where
  read  : (A : tp pos) (n : ℕ) (i : Fin n) (a : val A) → ArrayStep
  write : (A : tp pos) (n : ℕ) (i : Fin n) (a : val A) → ArrayStep
  alloc : (A : tp pos) (n : ℕ)                         → ArrayStep

record ArrayCostMonoid : Set₁ where
  field
    costMonoid : CostMonoid
    arrayCost  : (s : ArrayStep) → CostMonoid.ℂ costMonoid

ℕ-ArrayCostMonoid : ArrayCostMonoid
ℕ-ArrayCostMonoid = record
  { costMonoid = ℕ-CostMonoid
  ; arrayCost  = λ where
    (read  A n i a) → 1
    (write A n i a) → 1
    (alloc A n    ) → 0
  }

ℕ²-ArrayCostMonoid : ArrayCostMonoid
ℕ²-ArrayCostMonoid = record
  { costMonoid = ParCostMonoid.costMonoid ℕ²-ParCostMonoid
  ; arrayCost  = λ where
    (read  A n i a) → 1 , 1
    (write A n i a) → 1 , 1
    (alloc A n    ) → 0 , 0
  }

List-ArrayCostMonoid : (A : Set) (arrayCost : (s : ArrayStep) → A) → ArrayCostMonoid
List-ArrayCostMonoid A arrayCost = record
  { costMonoid = List-CostMonoid A
  ; arrayCost  = λ s → [ arrayCost s ]
  }

ArrayStep-List-ArrayCostMonoid : ArrayCostMonoid
ArrayStep-List-ArrayCostMonoid = List-ArrayCostMonoid ArrayStep λ s → s
