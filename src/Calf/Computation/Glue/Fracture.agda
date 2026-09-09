module Calf.Computation.Glue.Fracture where

open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path
  using (compPathlEquiv; compPathrEquiv; symIso)
open import Cubical.Foundations.Univalence using (ua)

open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Computation.Glue.Base

open import Calf.Value.Glue public

open Fractureᶜ

FractureGlueᶜ : 𝒞 → 𝒞
FractureGlueᶜ = fromFractureᶜ ∘ toFractureᶜ

glue•ᶜ : (F : Fractureᶜ) → ●ᶜ (fromFractureᶜ F) ≃ᶜ ⟨ F .A• ⟩ᶜ
glue•ᶜ F = ●ᶜ-rec (F .A•) (proj•ᶜ F) , equivIsEquiv (glue•-equiv (U-Fracture F))

glue◦ᶜ : (F : Fractureᶜ) → ◯ᶜ (fromFractureᶜ F) ≃ᶜ ⟨ F .A◦ ⟩ᶜ
glue◦ᶜ F = ◯ᶜ-rec (F .A◦) (proj◦ᶜ F) , equivIsEquiv (glue◦-equiv (U-Fracture F))

glue•-pathᶜ : (F : Fractureᶜ) → ●ᶜ• (fromFractureᶜ F) ≡ F .A•
glue•-pathᶜ F = 𝒞•-path (uaᶜ (glue•ᶜ F))

glue◦-pathᶜ : (F : Fractureᶜ) → ◯ᶜ◦ (fromFractureᶜ F) ≡ F .A◦
glue◦-pathᶜ F = 𝒞◦-path (uaᶜ (glue◦ᶜ F))

opaque
  glue-fracture-sectionᶜ : section toFractureᶜ fromFractureᶜ
  glue-fracture-sectionᶜ F =
    Fractureᶜ-path
      (glue•-pathᶜ F)
      (glue◦-pathᶜ F)
      (⊸-path
        (λ i → ⟨ glue•-pathᶜ F i ⟩ᶜ)
        (λ i → ●ᶜ ⟨ glue◦-pathᶜ F i ⟩ᶜ)
        (λ i → Fracture.χ• (glue-fracture-section (U-Fracture F) i)))

  glue-fracture-sectionᶜ-α• : (F : Fractureᶜ) →
    PathP
      (λ i →
        ⟨ glue•-pathᶜ F (~ i) ⟩ᶜ ⊸
        ●ᶜ ⟨ glue◦-pathᶜ F (~ i) ⟩ᶜ)
      (F .α•)
      (toFractureᶜ (fromFractureᶜ F) .α•)
  glue-fracture-sectionᶜ-α• F i =
    glue-fracture-sectionᶜ F (~ i) .α•

fractureᶜ : A ⊸ FractureGlueᶜ A
fractureᶜ .U = fracture
fractureᶜ {A} .charge c a = Glue-path (is-set (◯ᶜ A)) refl refl

opaque
  glue-fracture-retractᶜ : retract toFractureᶜ fromFractureᶜ
  glue-fracture-retractᶜ A =
    sym (conservativity fractureᶜ fracture-isEquiv)

fracture-and-gluingᶜ : 𝒞 ≃ Fractureᶜ
fracture-and-gluingᶜ =
  isoToEquiv
    (iso
      toFractureᶜ
      fromFractureᶜ
      glue-fracture-sectionᶜ
      glue-fracture-retractᶜ)

toSquareᶜ : (A ⊸ B) → Fractureᶜ-Square (toFractureᶜ A) (toFractureᶜ B)
toSquareᶜ f =
  (●ᶜ.map f , ◯ᶜ.map f) , ⊸-path refl refl (toSquare (U f) .snd)

fracture-and-gluing-squareᶜ : (A ⊸ B) ≃ Fractureᶜ-Square (toFractureᶜ A) (toFractureᶜ B)
fracture-and-gluing-squareᶜ {A} {B} =
    (A ⊸ B)
  ≃⟨ ⊸-postcomp-≃ fractureᶜ fracture-isEquiv ⟩
    (A ⊸ fromFractureᶜ (toFractureᶜ B))
  ≃⟨ ⊸-Glueᶜ-≃ {A} {toFractureᶜ B} ⟩
    (Σ[ (h• , h◦) ∈ (A ⊸ ●ᶜ B) × (A ⊸ ◯ᶜ B) ]
      (h• ⨾ᶜ ●ᶜ.map η◦ᶜ ≡ h◦ ⨾ᶜ η•ᶜ))
  ≃⟨ invEquiv (Σ-cong-equiv
       (≃-× (⊸-precomp-η•ᶜ-≃ (●ᶜ• B)) (⊸-precomp-η◦ᶜ-≃ (◯ᶜ◦ B)))
       (λ (f• , f◦) →
           congEquiv (⊸-precomp-η•ᶜ-≃ (●ᶜ• (◯ᶜ B)))
         ∙ₑ compPathlEquiv (sym (assoc-η f•))
         ∙ₑ compPathrEquiv (natural-η f◦))) ⟩
    Fractureᶜ-Square (toFractureᶜ A) (toFractureᶜ B)
  ■
  where
    opaque
      natural-η : (f◦ : ◯ᶜ A ⊸ ◯ᶜ B)
        → η•ᶜ {A} ⨾ᶜ (●ᶜ.map η◦ᶜ ⨾ᶜ ●ᶜ.map f◦) ≡ (η◦ᶜ ⨾ᶜ f◦) ⨾ᶜ η•ᶜ
      natural-η f◦ = ⊸-path refl refl refl

    opaque
      assoc-η : (f• : ●ᶜ A ⊸ ●ᶜ B)
        → η•ᶜ ⨾ᶜ (f• ⨾ᶜ ●ᶜ.map η◦ᶜ) ≡ (η•ᶜ ⨾ᶜ f•) ⨾ᶜ ●ᶜ.map η◦ᶜ
      assoc-η f• = ⊸-path refl refl refl
