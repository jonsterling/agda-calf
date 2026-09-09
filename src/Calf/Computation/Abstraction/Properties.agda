module Calf.Computation.Abstraction.Properties where

open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

open import Calf.Core.Abstract
open import Calf.Core.Cost using (ℂ)
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue as Glueᶜ hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Computation.Abstraction.Base

open Fractureᶜ

opaque
  unfolding Abstractionᶜ

  ●ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ●ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ●ᶜ A-⊤
  ●ᶜ-Abstractionᶜ {A-⊤} {A-abs} α =
    cong ⟨_⟩ᶜ (glue•-pathᶜ (Abstractionᶜ-Fracture A-⊤ A-abs α))

  ◯ᶜ-Abstractionᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ◯ᶜ (Abstractionᶜ A-⊤ A-abs α) ≡ ◯ᶜ A-abs
  ◯ᶜ-Abstractionᶜ {A-⊤} {A-abs} α =
    cong ⟨_⟩ᶜ (glue◦-pathᶜ (Abstractionᶜ-Fracture A-⊤ A-abs α))

opaque
  unfolding Abstractionᶜ triangleᶜ

  ●ᶜ-triangleᶜ-isEquiv : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
    → isEquiv (●ᶜ.map (triangleᶜ α) .U)
  ●ᶜ-triangleᶜ-isEquiv {A-⊤} {A-abs} α =
    composesToId→Equiv (equivFun ge) (●ᶜ.map (triangleᶜ α) .U) (funExt proj-unit) (ge .snd)
    where
      ge : U (●ᶜ (Abstractionᶜ A-⊤ A-abs α)) ≃ U (●ᶜ A-⊤)
      ge = glue•-equiv (U-Fracture (Abstractionᶜ-Fracture A-⊤ A-abs α))

      proj-unit : ∀ w → equivFun ge (●ᶜ.map (triangleᶜ α) .U w) ≡ w
      proj-unit = ●.elim (λ _ → ●.●-≡-isModal _ _) (λ _ → refl)

●ᶜ-Abstractionᶜ-≃ᶜ : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) → ●ᶜ A-⊤ ≃ᶜ ●ᶜ (Abstractionᶜ A-⊤ A-abs α)
●ᶜ-Abstractionᶜ-≃ᶜ α = ●ᶜ.map (triangleᶜ α) , ●ᶜ-triangleᶜ-isEquiv α

opaque
  unfolding Abstractionᶜ squareᶜ triangleᶜ

  triangleᶜ-natural : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (coh : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
    → triangleᶜ α ⨾ᶜ squareᶜ α β f-⊤ f-abs coh
      ≡ f-⊤ ⨾ᶜ triangleᶜ β
  triangleᶜ-natural {A-⊤} {A-abs} {α} {B-⊤} {B-abs} {β} f-⊤ f-abs coh =
    ⊸-path refl refl
      (funExt λ a →
        Glue-path (is-set (◯ᶜ B-abs))
          refl
          (funExt λ _ → sym (coh a)))

opaque
  unfolding Abstractionᶜ ●ᶜ-Abstractionᶜ

  Abstractionᶜ-coherence : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) →
    PathP
      (λ i →
        sym (●ᶜ-Abstractionᶜ α) i ⊸
        ●ᶜ (sym (◯ᶜ-Abstractionᶜ α) i))
      (●ᶜ.map (α ⨾ᶜ η◦ᶜ {A = A-abs}))
      (●ᶜ.map (η◦ᶜ {A = Abstractionᶜ A-⊤ A-abs α}))
  Abstractionᶜ-coherence {A-⊤} {A-abs} α =
    glue-fracture-sectionᶜ-α•
      (Abstractionᶜ-Fracture A-⊤ A-abs α)

opaque
  unfolding Abstractionᶜ

  Abstractionᶜ-open-≃
    : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
    → ⟨ ABS ⟩
    → Abstractionᶜ A-⊤ A-abs α ≃ᶜ A-abs
  Abstractionᶜ-open-≃ {A-⊤} {A-abs} α abs =
    Glueᶜ-open-≃ (Abstractionᶜ-Fracture A-⊤ A-abs α) abs ∙ₑᶜ ◯ᶜ-open-≃ abs

opaque
  unfolding Abstractionᶜ squareᶜ triangle-U Abstractionᶜ-open-≃

  Abstractionᶜ-open
    : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs)
    → ⟨ ABS ⟩
    → Abstractionᶜ A-⊤ A-abs α ≡ A-abs
  Abstractionᶜ-open α abs = uaᶜ (Abstractionᶜ-open-≃ α abs)

  square-openP
    : ∀ {A-⊤ A-abs B-⊤ B-abs}
    → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    → (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    → (f-coh : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤))
    → (abs : ⟨ ABS ⟩)
    → PathP
      (λ i →
        Abstractionᶜ-open α abs i
          ⊸ Abstractionᶜ-open β abs i)
      (squareᶜ α β f-⊤ f-abs f-coh)
      f-abs
  square-openP α β f-⊤ f-abs f-coh abs =
    ⊸-path
      (Abstractionᶜ-open α abs)
      (Abstractionᶜ-open β abs)
      (ua→
        {e = Abstractionᶜ-open-≃ α abs .fst .U
           , Abstractionᶜ-open-≃ α abs .snd}
        {B = λ i → U (Abstractionᶜ-open β abs i)}
        (λ _ →
          ua-gluePath
            ( Abstractionᶜ-open-≃ β abs .fst .U
            , Abstractionᶜ-open-≃ β abs .snd)
            refl))

  triangle-U-openP : ∀ {B-⊤ B-abs} (β : B-⊤ ⊸ B-abs)
      (b-⊤ : U B-⊤) (b-abs : U B-abs) (b-coh : β .U b-⊤ ≡ b-abs) (abs : ⟨ ABS ⟩) →
    PathP (λ i → U (Abstractionᶜ-open β abs i))
      (triangle-U β b-⊤ b-abs b-coh)
      b-abs
  triangle-U-openP β b-⊤ b-abs b-coh abs =
    ua-gluePath
      ( Abstractionᶜ-open-≃ β abs .fst .U
      , Abstractionᶜ-open-≃ β abs .snd)
      refl


opaque
  unfolding Abstractionᶜ squareᶜ

  squareᶜ-charge
    : ∀ {A-⊤ A-abs} (α : A-⊤ ⊸ A-abs) (c : ℂ)
    → (α-charge : (a : U A-⊤) → α .U (A-⊤ .charge c a) ≡ A-abs .charge c (α .U a))
    → squareᶜ α α
        (chargeᶜ {A-⊤} c) (chargeᶜ {A-abs} c)
        α-charge
      ≡ chargeᶜ {Abstractionᶜ A-⊤ A-abs α} c
  squareᶜ-charge {A-⊤} {A-abs} α c α-charge =
    ⊸-path
      refl
      refl
      (funExt λ _ → Glue-path (is-set (◯ᶜ A-abs)) refl refl)

  squareᶜ-⨾ᶜ : ∀ {A-⊤ A-abs α B-⊤ B-abs β C-⊤ C-abs γ}
    (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
    (fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a))
    (g-⊤ : B-⊤ ⊸ C-⊤) (g-abs : B-abs ⊸ C-abs)
    (gc : (b : U B-⊤) → γ .U (g-⊤ .U b) ≡ g-abs .U (β .U b))
    → squareᶜ α β f-⊤ f-abs fc ⨾ᶜ squareᶜ β γ g-⊤ g-abs gc
      ≡ squareᶜ α γ (f-⊤ ⨾ᶜ g-⊤) (f-abs ⨾ᶜ g-abs)
          (λ a → gc (f-⊤ .U a) ∙ cong (g-abs .U) (fc a))
  squareᶜ-⨾ᶜ {C-⊤ = C-⊤} {C-abs} {γ} f-⊤ f-abs fc g-⊤ g-abs gc =
    ⊸-path refl refl $ funExt λ a →
      Glue-path (is-set (◯ᶜ C-abs))
        (●.map-∘ (f-⊤ .U) (g-⊤ .U) (• a))
        (◯.map-∘ (f-abs .U) (g-abs .U) (◦ a))

  squareᶜ-≡ : ∀ {A-⊤ A-abs α B-⊤ B-abs β}
    {f-⊤ f-⊤' : A-⊤ ⊸ B-⊤} {f-abs f-abs' : A-abs ⊸ B-abs}
    {fc : (a : U A-⊤) → β .U (f-⊤ .U a) ≡ f-abs .U (α .U a)}
    {fc' : (a : U A-⊤) → β .U (f-⊤' .U a) ≡ f-abs' .U (α .U a)}
    → f-⊤ ≡ f-⊤' → f-abs ≡ f-abs'
    → squareᶜ α β f-⊤ f-abs fc ≡ squareᶜ α β f-⊤' f-abs' fc'
  squareᶜ-≡ {B-⊤ = B-⊤} {B-abs} {β} {fc = fc} {fc' = fc'} p q =
    ⊸-path refl refl $ funExt λ a →
      Glue-path (is-set (◯ᶜ B-abs))
        (cong (λ f → ●.map (f .U) (• a)) p)
        (cong (λ f → ◯.map (f .U) (◦ a)) q)

  Abstractionᶜ-fuse : ∀ {A-⊤ A-abs B-⊤ B-abs}
      (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
      (f-⊤ : A-⊤ ⊸ B-⊤) (f-abs : A-abs ⊸ B-abs)
      (f-coherence : (a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ≡ U f-abs (U α a-⊤)) →
    Abstractionᶜ
      (Abstractionᶜ A-⊤ A-abs α)
      (Abstractionᶜ B-⊤ B-abs β)
      (squareᶜ α β f-⊤ f-abs f-coherence)
    ≡ Abstractionᶜ A-⊤ B-abs (α ⨾ᶜ f-abs)
  Abstractionᶜ-fuse {A-⊤} {A-abs} {B-⊤} {B-abs} α β f-⊤ f-abs f-coherence =
    cong fromFractureᶜ $
    Fractureᶜ-path
      (glue•-pathᶜ (Abstractionᶜ-Fracture A-⊤ A-abs α))
      (glue◦-pathᶜ (Abstractionᶜ-Fracture B-⊤ B-abs β)) $
    ⊸-path
      (λ i → ⟨ glue•-pathᶜ (Abstractionᶜ-Fracture A-⊤ A-abs α) i ⟩ᶜ)
      (λ i → ●ᶜ ⟨ glue◦-pathᶜ (Abstractionᶜ-Fracture B-⊤ B-abs β) i ⟩ᶜ)
      (square-χ•-path
        (squareᶜ α β f-⊤ f-abs f-coherence .U)
        (●ᶜ.map ((α ⨾ᶜ f-abs) ⨾ᶜ η◦ᶜ) .U)
        (λ g →
            cong (●.map (◯.map (f-abs .U))) (sym (•→◦ g))
          ∙ ●.map-∘ ((α ⨾ᶜ η◦ᶜ) .U) (◯.map (f-abs .U)) (• g)))
