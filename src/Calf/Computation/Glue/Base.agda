module Calf.Computation.Glue.Base where

open import Cubical.Data.Sigma

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Open as ◯ᶜ

open import Calf.Value.Glue public

Glueᶜ : (A• A◦ : 𝒞) (α• : A• ⊸ ●ᶜ A◦) → 𝒞
Glueᶜ A• A◦ α• .U = Glue (U A•) (U A◦) (α• .U)
Glueᶜ A• A◦ α• .is-preorder = isPreorderGlue (A• .is-preorder) (A◦ .is-preorder)
Glueᶜ A• A◦ α• .charge c ((x• , x◦) , h) =
  (A• .charge c x• , A◦ .charge c x◦) ,
  α• .charge c x• ∙ cong (●ᶜ A◦ .charge c) h
Glueᶜ A• A◦ α• .charge-0 =
  Glue-path (is-set A◦) (A• .charge-0) (A◦ .charge-0)
Glueᶜ A• A◦ α• .charge-+ =
  Glue-path (is-set A◦) (A• .charge-+) (A◦ .charge-+)

record Fractureᶜ : 𝒱₁ where
  field
    A• : 𝒞•
    A◦ : 𝒞◦
    α• : ⟨ A• ⟩ᶜ ⊸ ●ᶜ ⟨ A◦ ⟩ᶜ
open Fractureᶜ

fromFractureᶜ : Fractureᶜ → 𝒞
fromFractureᶜ F = Glueᶜ ⟨ F .A• ⟩ᶜ ⟨ F .A◦ ⟩ᶜ (F .α•)

toFractureᶜ : 𝒞 → Fractureᶜ
toFractureᶜ A .A• = ●ᶜ• A
toFractureᶜ A .A◦ = ◯ᶜ◦ A
toFractureᶜ A .α• = ●ᶜ.map η◦ᶜ

proj•ᶜ : (F : Fractureᶜ) → fromFractureᶜ F ⊸ ⟨ F .A• ⟩ᶜ
proj•ᶜ F .U = •
proj•ᶜ F .charge c g = refl

proj◦ᶜ : (F : Fractureᶜ) → fromFractureᶜ F ⊸ ⟨ F .A◦ ⟩ᶜ
proj◦ᶜ F .U = ◦
proj◦ᶜ F .charge c g = refl

Fractureᶜ-path
  : {F G : Fractureᶜ}
  → (A•-path : F .A• ≡ G .A•)
  → (A◦-path : F .A◦ ≡ G .A◦)
  → PathP
      (λ i → A•-path i .fst ⊸ ●ᶜ (A◦-path i .fst))
      (F .α•)
      (G .α•)
  → F ≡ G
Fractureᶜ-path A•-path A◦-path α•-path i .A• = A•-path i
Fractureᶜ-path A•-path A◦-path α•-path i .A◦ = A◦-path i
Fractureᶜ-path A•-path A◦-path α•-path i .α• = α•-path i

Fractureᶜ-path-U :
  {F G : Fractureᶜ}
  → (p• : ⟨ F .A• ⟩ᶜ ≡ ⟨ G .A• ⟩ᶜ)
  → (p◦ : ⟨ F .A◦ ⟩ᶜ ≡ ⟨ G .A◦ ⟩ᶜ)
  → PathP
      (λ i → p• i ⊸ ●ᶜ (p◦ i))
      (F .α•)
      (G .α•)
  → F ≡ G
Fractureᶜ-path-U p• p◦ pα =
  Fractureᶜ-path
    (●ᶜ.𝒞•-path p•)
    (◯ᶜ.𝒞◦-path p◦)
    pα

U-Fracture : Fractureᶜ → Fracture
U-Fracture F =
  record
    { X• = U• (F .A•)
    ; X◦ = U◦ (F .A◦)
    ; χ• = F .α• .U
    }

Fractureᶜ-Square : Fractureᶜ → Fractureᶜ → 𝒱
Fractureᶜ-Square F G =
  Σ[ (f• , f◦) ∈ (⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ) × (⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ) ]
    f• ⨾ᶜ G .α• ≡ F .α• ⨾ᶜ ●ᶜ.map f◦

squareᶜ
  : ∀ {A• A◦ α B• B◦ β}
  → (f• : A• ⊸ B•)
  → (f◦ : A◦ ⊸ B◦)
  → f• ⨾ᶜ β ≡ α ⨾ᶜ ●ᶜ.map f◦
  → Glueᶜ A• A◦ α ⊸ Glueᶜ B• B◦ β
squareᶜ f• f◦ f-coherence .U =
  square
    (f• .U)
    (f◦ .U)
    (λ a• → cong ((_$ a•) ∘ U) f-coherence)
squareᶜ {B◦ = B◦} f• f◦ f-coherence .charge c q =
  Σ≡Prop (λ _ → is-set (●ᶜ B◦) _ _)
    (ΣPathP (f• .charge c (• q) , f◦ .charge c (◦ q)))

⊸-Glueᶜ-≃ : {A : 𝒞} {F : Fractureᶜ}
  → (A ⊸ fromFractureᶜ F)
  ≃ (Σ[ (h• , h◦) ∈ (A ⊸ ⟨ F .A• ⟩ᶜ) × (A ⊸ ⟨ F .A◦ ⟩ᶜ) ]
      (h• ⨾ᶜ F .α• ≡ h◦ ⨾ᶜ η•ᶜ))
⊸-Glueᶜ-≃ {A} {F} = isoToEquiv (iso fwd bwd sec ret)
  where
    fwd : (A ⊸ fromFractureᶜ F)
      → Σ[ (h• , h◦) ∈ (A ⊸ ⟨ F .A• ⟩ᶜ) × (A ⊸ ⟨ F .A◦ ⟩ᶜ) ]
          (h• ⨾ᶜ F .α• ≡ h◦ ⨾ᶜ η•ᶜ)
    fwd k = (k ⨾ᶜ proj•ᶜ F , k ⨾ᶜ proj◦ᶜ F) ,
      ⊸-path refl refl (funExt λ a → •→◦ (k .U a))

    bwd : (Σ[ (h• , h◦) ∈ (A ⊸ ⟨ F .A• ⟩ᶜ) × (A ⊸ ⟨ F .A◦ ⟩ᶜ) ]
            (h• ⨾ᶜ F .α• ≡ h◦ ⨾ᶜ η•ᶜ))
      → (A ⊸ fromFractureᶜ F)
    bwd ((h• , h◦) , coh) .U a =
      (h• .U a , h◦ .U a) , funExt⁻ (cong (λ w → w .U) coh) a
    bwd ((h• , h◦) , coh) .charge c a =
      Glue-path (is-set ⟨ F .A◦ ⟩ᶜ) (h• .charge c a) (h◦ .charge c a)

    sec : section fwd bwd
    sec ((h• , h◦) , coh) =
      Σ≡Prop (λ _ → isSet⊸ _ _)
        (ΣPathP (⊸-path refl refl refl , ⊸-path refl refl refl))

    ret : retract fwd bwd
    ret k = ⊸-path refl refl (funExt λ a →
      Σ≡Prop (λ _ → is-set (●ᶜ ⟨ F .A◦ ⟩ᶜ) _ _) refl)
