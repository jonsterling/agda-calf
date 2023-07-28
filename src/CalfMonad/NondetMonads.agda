{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.NondetMonads where

open Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Level using (lift; lower)

open import CalfMonad.NondetMonad
import CalfMonad.Monad as Monad
import CalfMonad.Monads as Monads

open NondetMonad

module DetMonad {ℓ ℓ′} {M : Set ℓ → Set ℓ′} (monad : Monad.Monad M) where
  open Monad.Monad monad

  nondetMonad : NondetMonad M
  nondetMonad .branch = pure (lift false)

module ListMonad ℓ where
  open Monads.ListMonad ℓ

  nondetMonad : NondetMonad M
  nondetMonad .branch = lift false ∷ lift true ∷ []

module MonadLift {ℓ ℓ′ ℓ″ ℓ‴ M M′} (monad : Monad.Monad M′) (monadLift : Monad.MonadLift {ℓ} {ℓ′} {ℓ″} {ℓ‴} M M′) (nondetMonad′ : NondetMonad {ℓ} {ℓ′} M) where
  open Monad.Monad monad

  nondetMonad : NondetMonad {ℓ″} {ℓ‴} M′
  nondetMonad .branch = monadLift .Monad.MonadLift.lift (nondetMonad′ .branch) λ b → pure (lift (lower b))
