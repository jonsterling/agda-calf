{-# OPTIONS --rewriting #-}

open import Algebra.Cost

module Calf.Data.BoundedFunction (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Step costMonoid
open import Calf.Data.IsBounded costMonoid

open import Level using (_⊔_)
open import Relation.Binary


Ψ : (A : tp⁺) → (B : val A → tp⁺) → (val A → ℂ) → tp⁺
Ψ A B p =
  Σ⁺ (U (Π A (λ a → F (B a)))) λ f →
  meta⁺ ((a : val A) → IsBounded (B a) (f a) (p a))

dom : ∀ {ℓ} {a} {A : Set a} {B : Set a} → Rel B ℓ → Rel (A → B) (a ⊔ ℓ)
dom {A = A} r f1 f2 = ∀ (a : A) → r (f1 a) (f2 a)

Ψ/relax : ∀ A B {p p'} → dom _≤_ p p' →
                 (f : val (Ψ A B p)) →
                 val (Ψ A B p')
Ψ/relax A B {p} {p'} h (func , prf) = func ,
  λ a → bound/relax {B a} (h a) {e = func a} (prf a)
