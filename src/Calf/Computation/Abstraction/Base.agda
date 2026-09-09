module Calf.Computation.Abstraction.Base where

open import Calf.Value
open import Calf.Value.Abstraction
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ

open Fractureᶜ

opaque
  Abstractionᶜ-Fracture : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → Fractureᶜ
  Abstractionᶜ-Fracture A-⊤ A-abs α .A• = ●ᶜ• A-⊤
  Abstractionᶜ-Fracture A-⊤ A-abs α .A◦ = ◯ᶜ◦ A-abs
  Abstractionᶜ-Fracture A-⊤ A-abs α .α• = ●ᶜ.map (α ⨾ᶜ η◦ᶜ)

  Abstractionᶜ : (A-⊤ A-abs : 𝒞) → (A-⊤ ⊸ A-abs) → 𝒞
  Abstractionᶜ A-⊤ A-abs α = fromFractureᶜ (Abstractionᶜ-Fracture A-⊤ A-abs α)

  squareᶜ
    : ∀ {A-⊤ A-abs B-⊤ B-abs}
    → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → Abstractionᶜ A-⊤ A-abs α ⊸ Abstractionᶜ B-⊤ B-abs β
  squareᶜ α β f-⊤ f-abs f-coherence =
    Glueᶜ.squareᶜ
      (●ᶜ.map f-⊤)
      (◯ᶜ.map f-abs)
      coh
    where
      coh : ●ᶜ.map f-⊤ ⨾ᶜ ●ᶜ.map (β ⨾ᶜ η◦ᶜ) ≡ ●ᶜ.map (α ⨾ᶜ η◦ᶜ) ⨾ᶜ ●ᶜ.map (◯ᶜ.map f-abs)
      coh =
        ⊸-path refl refl
          (funExt (●ᶜ.elim (λ _ → ●ᶜ.●-≡-isModal _ _) λ a → cong (η• ∘ η◦) (f-coherence a)))

  triangle-U : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) (a-⊤ : U A-⊤) (a-abs : U A-abs)
    → α .U a-⊤ ≡ a-abs
    → U (Abstractionᶜ A-⊤ A-abs α)
  triangle-U α = triangle (α .U)

opaque
  unfolding Abstractionᶜ

  triangleᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → A-⊤ ⊸ Abstractionᶜ A-⊤ A-abs α
  triangleᶜ α .U = triangle′ (α .U)
  triangleᶜ {A-abs = A-abs} α .charge c a =
    Glue-path (is-set (◯ᶜ A-abs)) refl (cong η◦ (α .charge c a))

  Abstractionᶜ-id : (A : 𝒞) → Abstractionᶜ A A idᶜ ≡ A
  Abstractionᶜ-id A =
    sym (conservativity (triangleᶜ idᶜ) fracture-isEquiv)

  triangleᶜ-id : PathP (λ i → A ⊸ Abstractionᶜ-id A i) (triangleᶜ idᶜ) idᶜ
  triangleᶜ-id {A} = ⊸-path refl (Abstractionᶜ-id A) triangle′-id

triangle-abs : ∀ {A-⊤ A-abs α B}
  → A-abs ⊸ B
  → Abstractionᶜ A-⊤ A-abs α ⊸ B
triangle-abs {α = α} {B} f-abs =
  subst (_ ⊸_) (Abstractionᶜ-id B) $
  squareᶜ α idᶜ (α ⨾ᶜ f-abs) f-abs (λ _ → refl)

triangle-⊤ : ∀ {A B-⊤ B-abs}
  → (β : B-⊤ ⊸ B-abs)
  → A ⊸ B-⊤
  → A ⊸ Abstractionᶜ B-⊤ B-abs β
triangle-⊤ β f-⊤ = f-⊤ ⨾ᶜ triangleᶜ β
