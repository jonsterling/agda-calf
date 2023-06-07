{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV {ℓ} {M : Set ℓ → Set ℓ} (monad : Monad M) where

open Monad monad

open Agda.Primitive
open import Agda.Builtin.Equality
open import Axiom.Extensionality.Propositional using (Extensionality)

tp+ : Set (lsuc ℓ)
tp+ = Set ℓ

record tp- : Set (lsuc ℓ) where
  field
    U : tp+
    bind : {A : tp+} → M A → (A → U) → U

    pure-bind : Extensionality ℓ ℓ → ∀ {A} a f → bind {A} (pure a) f ≡ f a
    >>=-bind : Extensionality ℓ ℓ → ∀ {A B} e f g → bind {B} (e >>= f) g ≡ bind {A} e λ a → bind (f a) g

open tp- public

F : tp+ → tp-
U (F A) = M A
bind (F B) = _>>=_
pure-bind (F B) ext = pure->>=
>>=-bind (F B) ext = >>=->>=

Π : (A : tp+) → (A → tp-) → tp-
U (Π A X) = ∀ a → U (X a)
bind (Π B X) e f b = bind (X b) e λ a → f a b
pure-bind (Π B X) ext a f = ext λ b → pure-bind (X b) ext a λ a → f a b
>>=-bind (Π C X) ext e f g = ext λ c → >>=-bind (X c) ext e f λ b → g b c
