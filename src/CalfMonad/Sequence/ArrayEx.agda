{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayEx where

open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.List.Base    using ([]; _∷_)
open import Data.Nat.Base     using (ℕ)
open import Data.Product      using (_,_)
open import Data.Vec.Base     using ([]; _∷_)

open import CalfMonad.CostMonad
open import CalfMonad.CostMonads
open import CalfMonad.CostMonoid
open import CalfMonad.CostMonoids
open import CalfMonad.Monad
open import CalfMonad.Sequence.Array
open import CalfMonad.Sequence.ArrayCostMonoid
open import CalfMonad.Sequence.ArraySig

module Ex {ℓ} {M : Set → Set ℓ} (monad : Monad M) (array : ARRAY M) where
  open Monad monad
  open ARRAY array

  ex : M (Array ℕ 3)
  ex = build do
    b₁  ← assign 0F 1
    b₃  ← assign 2F 3
    b₂  ← assign 1F 2
    b₁₃ ← join b₁ b₃
    join b₁₃ b₂

open Ex (WriterMonad.monad (List-CostMonoid _)) (array (WriterMonad.costMonad (List-CostMonoid _)) (ArrayStep-List-ArrayCostMonoid _)) public

module Ex′ {ℓ ℓ′} {M : Set → Set ℓ} {ℂ : Set ℓ′} {monad : Monad M} {costMonoid : CostMonoid ℂ} {costMonad : CostMonad monad costMonoid} {parCostMonoid : ParCostMonoid ℂ} (parCostMonad : ParCostMonad costMonad parCostMonoid) (array : ARRAY M) where
  open Monad monad
  open ParCostMonad parCostMonad
  open ARRAY array

  ex′ : M (Array ℕ 3)
  ex′ = build do
    b₁ , b₃ ← assign 0F 1 & assign 2F 3
    b₂      ← assign 1F 2
    b₁₃     ← join b₁ b₃
    join b₁₃ b₂

open Ex′ (WriterMonad.parCostMonad (CostGraph-CostMonoid _) (CostGraph-ParCostMonoid _)) (array (WriterMonad.costMonad (CostGraph-CostMonoid _)) (ArrayStep-CostGraph-ArrayCostMonoid _)) public
