open import Calf.CostMonoid

module Calf.Types.BoundedFunction (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.Types.Bounded costMonoid

open import Level using (_⊔_)
open import Relation.Binary
open import Data.Product

bounded : (A : tp pos) → cmp cost → tp neg
bounded A n = Σ+- (U (F A)) λ u → IsBounded⁻ A u n

Ψ : (A : tp pos) → (B : val A → tp pos) → (val A → ℂ) → tp neg
Ψ A B p =
  Σ+- (U(Π A (λ a → F (B a)))) λ f →
    Π A λ a → IsBounded⁻ (B a) (f a) (p a)

dom : ∀ {ℓ} {a} {A : Set a} {B : Set a} → Rel B ℓ → Rel (A → B) (a ⊔ ℓ)
dom {A = A} r f1 f2 = ∀ (a : A) → r (f1 a) (f2 a)

Ψ/relax : ∀ A B {p p'} → dom _≤_ p p' →
                 (f : cmp (Ψ A B p)) →
                 cmp (Ψ A B p')
Ψ/relax A B h (func , prf) = func ,
  λ a → bound/relax (λ _ → h a) (prf a)
