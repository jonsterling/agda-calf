{-# OPTIONS --erased-cubical --safe #-}

module CalfMonad.Prelude where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Equality

private module _ {a A x y} where
  ≡⇒Path : x ≡ y → PathP {a} (λ _ → A) x y
  ≡⇒Path refl _ = x

  Path⇒≡ : PathP {a} (λ _ → A) x y → x ≡ y
  Path⇒≡ p = primTransp (λ i → x ≡ p i) i0 refl

funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g
funext eqv = Path⇒≡ λ i x → ≡⇒Path (eqv x) i
