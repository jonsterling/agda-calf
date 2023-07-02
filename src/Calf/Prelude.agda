{-# OPTIONS --without-K #-}

module Calf.Prelude where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite public

Ω = Prop
□ = Set

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g
  funext/Ω : {A : Prop} {B : □} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
