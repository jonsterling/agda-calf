module Calf.Computation.Power where

open import Calf.Value
open import Calf.Value.Pi
open import Calf.Computation

Πᶜ : (X : 𝒱) → (X → 𝒞) → 𝒞
Πᶜ X A .U = (x : X) → U (A x)
Πᶜ X A .is-preorder = isPreorderΠ λ x → A x .is-preorder
Πᶜ X A .charge c e x = A x .charge c (e x)
Πᶜ X A .charge-0 {e} = funExt λ x → A x .charge-0 {e x}
Πᶜ X A .charge-+ {e} {c₁} {c₂} = funExt λ x → A x .charge-+ {e x} {c₁} {c₂}

syntax Πᶜ X (λ x → A) = [ x ∈ X ] ⇀ A

infixr 2 _⇀_

_⇀_ : 𝒱 → 𝒞 → 𝒞
X ⇀ A = [ _ ∈ X ] ⇀ A

opaque
  ⇀-lam : (X → A ⊸ B) → A ⊸ (X ⇀ B)
  ⇀-lam e .U a x = e x .U a
  ⇀-lam e .charge c a = funExt λ x → e x .charge c a

  ⇀-app : A ⊸ (X ⇀ B) → X → A ⊸ B
  ⇀-app e x .U a = e .U a x
  ⇀-app e x .charge c a = cong (_$ x) (e .charge c a)

  Πᶜ-lam : {C : X → 𝒞} → ((x : X) → A ⊸ C x) → A ⊸ Πᶜ X C
  Πᶜ-lam e .U a x = e x .U a
  Πᶜ-lam e .charge c a = funExt λ x → e x .charge c a

  Πᶜ-app : {C : X → 𝒞} (x : X) → Πᶜ X C ⊸ C x
  Πᶜ-app x .U e = e x
  Πᶜ-app x .charge c e = refl
