module Calf.Computation.Copower where

open import Calf.Value
open import Calf.Value.Unit
open import Calf.Computation

open import Calf.Value.Product public
open import Calf.Value.Sigma public

Σᶜ : (X : 𝒱) (A : X → 𝒞) → isPreorder (Σ X (U ∘ A)) → 𝒞
Σᶜ X A h .U = Σ X (U ∘ A)
Σᶜ X A h .is-preorder = h
Σᶜ X A h .charge c (x , a) = x , A x .charge c a
Σᶜ X A h .charge-0 {x , _} = cong (x ,_) (A x .charge-0)
Σᶜ X A h .charge-+ {x , _} = cong (x ,_) (A x .charge-+)

Σᶜ₌ : (X₌ : 𝒱₌) → (⟨ X₌ ⟩ → 𝒞) → 𝒞
Σᶜ₌ X₌ A = Σᶜ ⟨ X₌ ⟩ A (isPreorderΣ X₌ λ x → A x .is-preorder)

syntax Σᶜ₌ X₌ (λ x → A) = [ x ∈ X₌ ] ⋊ A

Σᶜ-irrelevant : {X : 𝒱} {A : X → 𝒞} (h h' : isPreorder (Σ X (U ∘ A)))
  → Σᶜ X A h ≡ Σᶜ X A h'
Σᶜ-irrelevant h h' = 𝒞-path refl refl

module _ {X : 𝒱} {A : X → 𝒞} {h : isPreorder (Σ X (U ∘ A))} where
  Σᶜ-in : (x : X) → A x ⊸ Σᶜ X A h
  Σᶜ-in x .U a = x , a
  Σᶜ-in x .charge c a = refl

  Σᶜ-rec : ((x : X) → A x ⊸ B) → Σᶜ X A h ⊸ B
  Σᶜ-rec f .U (x , a) = f x .U a
  Σᶜ-rec f .charge c (x , a) = f x .charge c a

Σᶜ-map : {A B : X → 𝒞}
  {hA : isPreorder (Σ X (U ∘ A))} {hB : isPreorder (Σ X (U ∘ B))}
  → ((x : X) → A x ⊸ B x) → Σᶜ X A hA ⊸ Σᶜ X B hB
Σᶜ-map f .U (x , a) = x , f x .U a
Σᶜ-map f .charge c (x , a) = cong (x ,_) (f x .charge c a)

Σᶜ-map-idᶜ : {A : X → 𝒞} {h : isPreorder (Σ X (U ∘ A))} →
  Σᶜ-map {hA = h} {hB = h} (λ x → idᶜ {A = A x}) ≡ idᶜ
Σᶜ-map-idᶜ = ⊸-path refl refl refl

Σᶜ-map-⨾ᶜ : {A B C : X → 𝒞}
  {hA : isPreorder (Σ X (U ∘ A))}
  {hB : isPreorder (Σ X (U ∘ B))}
  {hC : isPreorder (Σ X (U ∘ C))}
  (f : (x : X) → A x ⊸ B x)
  (g : (x : X) → B x ⊸ C x) →
  Σᶜ-map {hA = hA} {hB = hB} f ⨾ᶜ Σᶜ-map {hA = hB} {hB = hC} g ≡
  Σᶜ-map {hA = hA} {hB = hC} (λ x → f x ⨾ᶜ g x)
Σᶜ-map-⨾ᶜ f g = ⊸-path refl refl refl

Σᶜ-1ᵛ : Σᶜ₌ 1ᵛ₌ (λ _ → A) ≡ A
Σᶜ-1ᵛ =
  conservativity
    (Σᶜ-rec λ _ → idᶜ)
    (isoToIsEquiv (iso _ (λ c → tt , c) (λ _ → refl) (λ _ → refl)))

_⋊_ : 𝒱ₚ → 𝒞 → 𝒞
Xₚ ⋊ A = Σᶜ ⟨ Xₚ ⟩ (const A) (isPreorder× (str Xₚ) (A .is-preorder))
