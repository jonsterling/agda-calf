{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.NondetMonads where

open Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Level using (lift; lower)

open import CalfMonad.CostMonoid
open import CalfMonad.Monad
open import CalfMonad.NondetMonad
import CalfMonad.CostMonads as CostMonads
import CalfMonad.Monads as Monads

open NondetMonad

module DetMonad {ℓ ℓ′} {M : Set ℓ → Set ℓ′} (monad : Monad M) where
  open Monad monad

  nondetMonad : NondetMonad M
  nondetMonad .branch = pure (lift false)

module ListMonad ℓ where
  open Monads.ListMonad ℓ

  nondetMonad : NondetMonad M
  nondetMonad .branch = lift false ∷ lift true ∷ []

module WriterMonadT ℓ {ℓ′ ℓ″} {M = M′ : Set (ℓ ⊔ ℓ″) → Set ℓ′} {ℂ : Set ℓ″} (monad′ : Monad M′) (costMonoid : CostMonoid ℂ) (nondetMonad′ : NondetMonad M′) where
  open Monad monad′
  open CostMonads.WriterMonadT ℓ monad′ costMonoid

  nondetMonad : NondetMonad M
  nondetMonad .branch = nondetMonad′ .branch >>= λ b → monad .Monad.pure (lift (lower b))
