module Calf.Computation.Glue.Properties where

open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Computation.Glue.Base
open import Calf.Computation.Glue.Fracture

open import Calf.Value.Glue public

open Fractureᶜ

fracture-map
  : (f : A ⊸ B)
  → FractureGlueᶜ A ⊸ FractureGlueᶜ B
fracture-map f = squareᶜ (●ᶜ.map f) (◯ᶜ.map f) (toSquareᶜ f .snd)

fracture-map-coh
  : (f : A ⊸ B)
  → (q• : U (●ᶜ A))
  → (q◦ : U (◯ᶜ A))
  → (qcoh : ●ᶜ.map (η◦ᶜ {A = A}) .U q• ≡ η• q◦)
  → ●.map (η◦ᶜ {A = B} .U) (●ᶜ.map f .U q•)
    ≡ η• (◯.map (f .U) q◦)
fracture-map-coh f q• q◦ qcoh =
  •→◦ (fracture-map f .U ((q• , q◦) , qcoh))

fracture-map-fracture
  : (f : A ⊸ B) (a : U A)
  → fracture-map f .U (fracture {X = U A} a) ≡ fracture {X = U B} (f .U a)
fracture-map-fracture {A} {B} f a =
  Σ≡Prop (λ _ → is-set (●ᶜ (◯ᶜ B)) _ _) refl

Glueᶜ-open-≃ : (F : Fractureᶜ) → ⟨ ABS ⟩ → fromFractureᶜ F ≃ᶜ ⟨ F .A◦ ⟩ᶜ
Glueᶜ-open-≃ F abs =
  proj◦ᶜ F , Glue-open-≃ (U-Fracture F) abs .snd

Glueᶜ-open : (F : Fractureᶜ) → ⟨ ABS ⟩ → fromFractureᶜ F ≡ ⟨ F .A◦ ⟩ᶜ
Glueᶜ-open F abs = uaᶜ (Glueᶜ-open-≃ F abs)

squareᶜ-openP : {F G : Fractureᶜ}
  → (f• : ⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) (f◦ : ⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ)
  → (coh : f• ⨾ᶜ G .α• ≡ F .α• ⨾ᶜ ●ᶜ.map f◦) (abs : ⟨ ABS ⟩)
  → PathP (λ i → Glueᶜ-open F abs i ⊸ Glueᶜ-open G abs i)
      (squareᶜ f• f◦ coh)
      f◦
squareᶜ-openP {F} {G} f• f◦ coh abs =
  uaᶜ-⊸ (Glueᶜ-open-≃ F abs) (Glueᶜ-open-≃ G abs) (⊸-path refl refl refl)
