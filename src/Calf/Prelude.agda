{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Prelude where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
open import Data.Product using (Σ; proj₁; proj₂; _×_; _,_; ∃) public

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

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g
  funext/Ω : {A : Prop} {B : □} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

record iso (A B : □) : □ where
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → fwd (bwd x) ≡ x
    bwd-fwd : ∀ x → bwd (fwd x) ≡ x
