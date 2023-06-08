{-# OPTIONS --cubical-compatible --safe #-}

open Agda.Primitive

open import CalfMonad.Monad

module CalfMonad.CBPV.Pi {ℓ ℓ′} {M : Set ℓ → Set (ℓ ⊔ ℓ′)} (monad : Monad M) where

open import CalfMonad.CBPV monad

Π : (A : tp+) → (A → tp-) → tp-
U (Π A X) = ∀ a → U (X a)
bind (Π B X) e f b = bind (X b) e λ a → f a b
pure-bind (Π B X) ext a f = ext λ b → pure-bind (X b) ext a λ a → f a b
>>=-bind (Π C X) ext e f g = ext λ c → >>=-bind (X c) ext e f λ b → g b c
