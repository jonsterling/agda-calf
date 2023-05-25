{-# OPTIONS --lossy-unification --erased-cubical --prop --rewriting #-}

module Examples.Sequence.ArrayEx2 where

open import Calf.CostMonoid
open import Examples.Sequence.CostGraph
open import Examples.Sequence.ArrayCostMonoid

parCostMonoid = CostGraph-ParCostMonoid ArrayStep

open import Examples.Sequence.ArraySig
open import Examples.Sequence.Array record
  { costMonoid = ParCostMonoid.costMonoid parCostMonoid
  ; arrayCost  = base
  }

open import Calf.Metalanguage
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Nat

open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.Product      using (_,_)
open import Data.Vec          using ([]; _∷_)
open import Function          using (_$_)

open ARRAY Array

ex : cmp (F (array nat _))
ex = mk 3 $
  bind _ (assign _ 0F 1 & (assign _ 2F 3 & assign _ 1F 2)) λ (u₁ , u₃ , u₂) →
  bind _ (join _ _ u₁ _ u₂) λ u₁₂ →
  join _ _ u₁₂ _ u₃
_ = {! ex !}
