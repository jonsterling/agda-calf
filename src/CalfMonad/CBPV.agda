{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV {ℓ} {M : Set ℓ → Set ℓ} (monad : Monad M) where

open Monad monad

open Agda.Primitive
open import Agda.Builtin.Equality
open import Axiom.Extensionality.Propositional using (Extensionality)

data tp+ : Set (lsuc ℓ)
data tp- : Set (lsuc ℓ)

val : tp+ → Set ℓ
cmp : tp- → Set ℓ

data tp+ where
  U : tp- → tp+
  meta : Set ℓ → tp+

data tp- where
  F : tp+ → tp-
  Π : ∀ A → (val A → tp-) → tp-

val (U X) = cmp X
val (meta A) = A

cmp (F A) = M (val A)
cmp (Π A X) = ∀ a → cmp (X a)

bind : ∀ {A X} → cmp (F A) → (val A → cmp X) → cmp X
bind {A} {F B} = _>>=_
bind {A} {Π B X} e f b = bind {A} {X b} e λ a → f a b

module _ (ext : Extensionality ℓ ℓ) where
  pure-bind : ∀ {A X} a f → bind {A} {X} (pure a) f ≡ f a
  pure-bind {A} {F B} = pure->>=
  pure-bind {A} {Π B X} a f = ext λ b → pure-bind {A} {X b} a λ a → f a b

  bind-bind : ∀ {A B X} e f g → bind {B} {X} (bind {A} {F B} e f) g ≡ bind {A} {X} e λ a → bind {B} {X} (f a) g
  bind-bind {A} {B} {F C} = >>=->>=
  bind-bind {A} {B} {Π C X} e f g = ext λ c → bind-bind {A} {B} {X c} e f λ b → g b c

infixr 3 Π
syntax Π A (λ _ → X) = A ⇒ X
