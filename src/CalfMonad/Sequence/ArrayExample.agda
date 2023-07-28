{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayExample where

open Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.Vec.Base     using ([]; _∷_)

open import CalfMonad.CostMonads
open import CalfMonad.CostMonoids
open import CalfMonad.Monad
open import CalfMonad.Monads
open import CalfMonad.NondetMonads

open import CalfMonad.Sequence.Array lzero

open WriterMonadT lzero (ListMonad.monad _) (CostGraph-CostMonoid ArrayStep)
open Imp monad (MonadLift.nondetMonad monad monadLift (ListMonad.nondetMonad _)) (parCostMonad (CostGraph-ParCostMonoid _)) (CostGraph-Step λ s → s)
open Array
open ArrayBuilder

ex₁ : M (Array Nat 3)
ex₁ = build (seq (seq (assign 0F 1) (assign 2F 3))
                 (seq (assign 1F 4) (assign 1F 2)))

ex₂ : M (Array Nat 3)
ex₂ = build (par (par (assign 0F 1) (assign 2F 3))
                 (par (assign 1F 4) (assign 1F 2)))
