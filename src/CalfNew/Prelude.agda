{-# OPTIONS --cubical-compatible --rewriting #-}

module CalfNew.Prelude where

open import Agda.Builtin.Equality public
import Agda.Builtin.Equality.Rewrite

postulate
  funext : {A : Set} {B : A → Set} {f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
