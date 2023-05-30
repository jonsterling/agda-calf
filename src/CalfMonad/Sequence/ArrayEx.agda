{-# OPTIONS --cubical-compatible --allow-unsolved-metas #-}

module CalfMonad.Sequence.ArrayEx where

open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.List.Base    using ([]; _∷_)
open import Data.Nat.Base     using (ℕ)
open import Data.Product      using (_,_)
open import Data.Vec.Base     using ([]; _∷_)
open import Level.Literals    using (#_)

open import CalfMonad.CostMonad
open import CalfMonad.CostMonads
open import CalfMonad.Sequence.Array
open import CalfMonad.Sequence.ArrayCostMonoid
open import CalfMonad.Sequence.ArraySig

module Ex costMonoid costMonad array where
  open CostMonad {# 1} {# 0} {# 1} {costMonoid} costMonad public
  open ARRAY {costMonad = costMonad} array

  ex : M (Array ℕ 3)
  ex = build do
    b₁  ← assign 0F 1
    b₃  ← assign 2F 3
    b₂  ← assign 1F 2
    b₁₂ ← join b₁ b₂
    join b₁₂ b₃

open Ex _ (costMonad _ _ _) (array _ _ _ (ArrayStep-List-ArrayCostMonoid _) _) public
