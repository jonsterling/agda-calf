{-# OPTIONS --cubical-compatible --lossy-unification --safe #-}

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

ret : ∀ {A} → val A → cmp (F A)
ret = pure

bind : ∀ {A X} → cmp (F A) → (val A → cmp X) → cmp X
bind {A} {F B} = _>>=_
bind {A} {Π B X} e f b = bind e λ a → f a b

infix 4 _≈_

_≈_ : ∀ {X} → cmp X → cmp X → Set ℓ
_≈_ {F A} = _≡_
_≈_ {Π A X} f g = ∀ a → f a ≈ g a

module _ (ext : Extensionality ℓ ℓ) where
  ≈⇒≡ : ∀ {X} {x y : cmp X} → x ≈ y → x ≡ y
  ≈⇒≡ {F A} x≈y = x≈y
  ≈⇒≡ {Π A X} x≈y = ext λ a → ≈⇒≡ (x≈y a)

ret-bind : ∀ {A X} a f → bind {A} {X} (ret a) f ≈ f a
ret-bind {A} {F B} = pure->>=
ret-bind {A} {Π B X} a f b = ret-bind a λ a → f a b

bind-ret : ∀ {A} e → bind {A} e ret ≡ e
bind-ret = >>=-pure

bind-bind : ∀ {A B X} e f g → bind {B} {X} (bind {A} e f) g ≈ bind e λ a → bind (f a) g
bind-bind {A} {B} {F C} = >>=->>=
bind-bind {A} {B} {Π C X} e f g c = bind-bind e f λ b → g b c

infixr 3 Π
syntax Π A (λ _ → X) = A ⇒ X
