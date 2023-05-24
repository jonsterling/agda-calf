{-# OPTIONS --lossy-unification --prop --rewriting #-}

module Examples.Sequence.ArrayEx where

open import Examples.Sequence.ArrayCostMonoid
open import Examples.Sequence.ArraySig
open import Examples.Sequence.Array ArrayStep-List-ArrayCostMonoid

open import Calf.Metalanguage
open import Calf.Types.Nat

open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.List         using ([]; _∷_)
open import Data.Vec          using ([]; _∷_)
open import Function          using (_$_)

open ARRAY Array

ex : cmp (F (array nat _))
ex = mk 3 $
  bind _ (assign _ 0F 1)    λ u₁  →
  bind _ (assign _ 2F 3)    λ u₃  →
  bind _ (assign _ 1F 2)    λ u₂  →
  bind _ (join _ _ u₁ _ u₂) λ u₁₂ →
  join _ _ u₁₂ _ u₃
_ = {! ex !}

fixmeEx : cmp (F (array nat 1))
fixmeEx =
  bind _ (assign _ 0F 1) λ u →
  mk _ $ ret u
_ = {! fixmeEx !}
