{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf.BoundedFunction (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.Upper costMonoid

open import Level using (_⊔_)
open import Relation.Binary
open import Data.Product

bounded : (A : tp pos) → val cost → tp pos
bounded A n = Σ++ (U (F A)) λ u → ub⁻ A u n

Ψ : (A : tp pos) → (B : val A → tp pos) → (val A → ℂ) → tp neg
Ψ A B p =
  Σ+- (U(Π A (λ a → F (B a)))) λ f →
    Π A λ a → F (ub⁻ (B a) (f a) (p a))

dom : ∀ {ℓ} {a} {A : Set a} {B : Set a} → Rel B ℓ → Rel (A → B) (a ⊔ ℓ)
dom {A = A} r f1 f2 = ∀ (a : A) → r (f1 a) (f2 a)

Ψ/relax : ∀ A B {p p'} → dom _≤_ p p' →
                 (f : cmp (Ψ A B p)) →
                 cmp (Ψ A B p')
Ψ/relax A B {p' = p'} h (func , prf) = func ,
  λ a →
    bind (F (ub⁻ (B a) (func a) (p' a))) (prf a) λ bound →
      ret (ub/relax (λ _ → h a) bound)
