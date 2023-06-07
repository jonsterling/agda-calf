{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArrayEx where

open Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Data.Fin.Base     using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F)
open import Data.Vec.Base     using ([]; _∷_)

open import CalfMonad.CostMonoids
open import CalfMonad.Monad
open import CalfMonad.Monads
open import CalfMonad.NondetMonads
open import CalfMonad.Sequence.ArrayCostMonoid
open import CalfMonad.Sequence.ArraySig
import CalfMonad.CostMonads as CostMonads
import CalfMonad.Sequence.Array as Array

data ArrayStep′ : Set where
  read  : ∀ {n} (i : Fin n) → ArrayStep′
  write : ∀ {n} (i : Fin n) → ArrayStep′
  alloc : (n : Nat)         → ArrayStep′

open CostMonads.WriterMonadT _ (ListMonad.monad lzero) (CostGraph-CostMonoid ArrayStep′)

Array = Array.Array
  (parCostMonad (CostGraph-ParCostMonoid _))
  (CostGraph-ArrayCostMonoid monad λ { (read as i) → read i ; (write i a) → write i ; (alloc A n) → alloc n })
  (WriterMonadT.nondetMonad _ (ListMonad.monad _) (CostGraph-CostMonoid _) (ListMonad.nondetMonad _))

module Ex {M : Set → Set} {monad : Monad M} (Array : ARRAY monad) where
  open ARRAY Array

  open import CalfMonad.CBPV monad
  open import CalfMonad.CBPV.Types.Nat monad

  ex : cmp (F (array nat 3))
  ex = build _ (seq _
    _ (seq _ _ (assign _ 0F 1) _ (assign _ 2F 3))
    _ (seq _ _ (assign _ 1F 4) _ (assign _ 1F 2))
    )

open Ex Array public

module Ex′ {M : Set → Set} {monad : Monad M} (Array : ARRAY monad) where
  open ARRAY Array

  open import CalfMonad.CBPV monad
  open import CalfMonad.CBPV.Types.Nat monad

  ex′ : cmp (F (array nat 3))
  ex′ = build _ (seq _
    _ (par _ _ (assign _ 0F 1) _ (assign _ 2F 3))
    _ (par _ _ (assign _ 1F 4) _ (assign _ 1F 2))
    )

open Ex′ Array public
