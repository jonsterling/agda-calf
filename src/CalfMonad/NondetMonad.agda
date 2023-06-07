{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.NondetMonad where

open import Agda.Builtin.Bool
open import Level using (Lift)

record NondetMonad {ℓ ℓ′} (M : Set ℓ → Set ℓ′) : Set ℓ′ where
  field
    branch : M (Lift ℓ Bool)
