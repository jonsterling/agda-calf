{-# OPTIONS --rewriting --cubical #-}

module Calf.Prelude where

open import Cubical.Core.Everything
open import Agda.Builtin.Equality.Rewrite public

Ω = Prop
□ = Set

funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g
funext h i a = h a i

funext/Ω : {A : Prop} {B : □} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
funext/Ω h i a = h a i
