{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf.BoundedFunction (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction costMonoid
open import Calf.Upper costMonoid
open import Relation.Binary
open import Level using (Level; _⊔_)
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Data.Nat.Induction
open import Function.Base
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.HeterogeneousEquality as H
open import Data.Product
open import Data.Product.Properties
open import Function.Bundles
open import Induction
import Level as L

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level

bounded : (A : tp pos) → cmp cost → tp neg
bounded A n = Σ+- (U (F A)) λ u → ub⁻ A u n

Ψ : (A : tp pos) → (B : val A → tp pos) → (val A → ℂ) → tp neg
Ψ A B p =
  Σ+- (U(Π A (λ a → F (B a)))) λ f →
    Π A λ a → ub⁻ (B a) (f a) (p a)

dom : ∀ {ℓ} {a} {A : Set a} {B : Set a} → Rel B ℓ → Rel (A → B) (a L.⊔ ℓ)
dom {A = A} r f1 f2 = ∀ (a : A) → r (f1 a) (f2 a)

open iso

Ψ/relax : ∀ A B {p p'} → dom _≤_ p p' →
                 (f : cmp (Ψ A B p)) →
                 cmp (Ψ A B p')
Ψ/relax A B h (func , prf) = func ,
  λ a → ub⁻/decode .fwd (ub/relax (h a) (ub⁻/decode .bwd (prf a)))
