{-# OPTIONS --prop --rewriting #-}

module Prelude where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Sigma public

Ω = Prop
□ = Set

data image (A B : □) (f : A → B) : B → Ω where
  image/in : (x : A) → image A B f (f x)

record sub (A : □) (ϕ : A → Ω) : □ where
  constructor sub/in
  field
    sub/wit : A
    sub/prf : ϕ sub/wit

open sub public

symm : {A : □} {a b : A} → a ≡ b → b ≡ a
symm refl = refl

record iso (A B : □) : □ where
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    bwd-fwd : ∀ x → bwd (fwd x) ≡ x