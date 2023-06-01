{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayEx where

open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.List.Base    using ([]; _∷_)
open import Data.Nat.Base     using (ℕ)
open import Data.Product      using (_,_)
open import Data.Vec.Base     using ([]; _∷_)
open import Level.Literals    using (#_)

open import CalfMonad.CostMonads
open import CalfMonad.Monad
open import CalfMonad.Sequence.Array
open import CalfMonad.Sequence.ArrayCostMonoid
open import CalfMonad.Sequence.ArraySig

module Ex monad array where
  open Monad {# 0} {# 1} monad
  open ARRAY {monad = monad} array

  ex : M (Array ℕ 3)
  ex = build do
    b₁  ← assign 0F 1
    b₃  ← assign 2F 3
    b₂  ← assign 1F 2
    b₁₂ ← join b₁ b₂
    join b₁₂ b₃

open Ex _ (array _ _ _ (ArrayStep-List-ArrayCostMonoid _) (costMonad _ _ _)) public
