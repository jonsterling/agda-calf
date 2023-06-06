{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.Unit {ℓ} {M : Set ℓ → Set ℓ} (monad : Monad M) where

open import Data.Unit.Polymorphic.Base using (⊤; tt) public

open import CalfMonad.CBPV monad

unit : tp+
unit = meta ⊤
