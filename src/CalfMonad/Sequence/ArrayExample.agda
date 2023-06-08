{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayExample where

open Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Data.Fin.Base     using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.Vec.Base     using ([]; _∷_)

open import CalfMonad.CostMonads
open import CalfMonad.CostMonoids
open import CalfMonad.Monads
open import CalfMonad.NondetMonads as NondetMonads using (module ListMonad)
import CalfMonad.CBPV as CBPV

open import CalfMonad.Sequence.Array
open import CalfMonad.Sequence.ArrayCostMonoid lzero
open import CalfMonad.Sequence.ArraySig

open WriterMonadT lzero (ListMonad.monad _) (CostGraph-CostMonoid ArrayStep)

module Ex {ℓ} {φ : Set ℓ} (array : ARRAY monad φ) where
  open ARRAY array

  ex : M (Array Nat 3)
  ex = build (seq (seq (assign 0F 1) (assign 2F 3))
                  (seq (assign 1F 4) (assign 1F 2)))

  ex′ : M (Array Nat 3)
  ex′ = build (seq (par (assign 0F 1) (assign 2F 3))
                   (par (assign 1F 4) (assign 1F 2)))

open Ex (array
  (parCostMonad (CostGraph-ParCostMonoid _))
  ArrayStep-CostGraph-ArrayCostMonoid
  (NondetMonads.WriterMonadT.nondetMonad _ (ListMonad.monad _) (CostGraph-CostMonoid _) (ListMonad.nondetMonad _))
  ) public
