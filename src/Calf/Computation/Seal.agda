module Calf.Computation.Seal where

open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Value.Seal
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue
  using (Fractureᶜ; toFractureᶜ; fromFractureᶜ; glue-fracture-sectionᶜ; proj•ᶜ; proj◦ᶜ)
open import Calf.Computation.Open as ◯ᶜ

private
  thin● : (A : 𝒞) → isThin (● (U A))
  thin● A = isPreorder→isThin (isPreorder● (A .is-preorder))

Glueᵈᶜ : (A• A◦ : 𝒞) (α• : A• ⊸ ●ᶜ A◦) → 𝒞
Glueᵈᶜ A• A◦ α• .U = Glueᵈ (U A•) (U A◦) (U α•)
Glueᵈᶜ A• A◦ α• .is-preorder =
  isPreorderGlueᵈ (U A•) (U A◦)
    (A• .is-preorder)
    (A◦ .is-preorder)
Glueᵈᶜ A• A◦ α• .charge c ((x• , x◦) , p) =
  (A• .charge c x• , A◦ .charge c x◦) ,
  ≡∙⊑ (α• .charge c x•) (⊑-mono (●ᶜ A◦ .charge c) p)
Glueᵈᶜ A• A◦ α• .charge-0 =
  Σ≡Prop (λ _ → thin● A◦ _ _)
    (ΣPathP (A• .charge-0 , A◦ .charge-0))
Glueᵈᶜ A• A◦ α• .charge-+ =
  Σ≡Prop (λ _ → thin● A◦ _ _)
    (ΣPathP (A• .charge-+ , A◦ .charge-+))

open Fractureᶜ

fromFractureᵈᶜ : Fractureᶜ → 𝒞
fromFractureᵈᶜ F = Glueᵈᶜ ⟨ F .A• ⟩ᶜ ⟨ F .A◦ ⟩ᶜ (F .α•)

Sealᶜ : 𝒞 → 𝒞
Sealᶜ = fromFractureᵈᶜ ∘ toFractureᶜ

proj•ᶜᵈ : Sealᶜ A ⊸ ●ᶜ A
proj•ᶜᵈ .U = •
proj•ᶜᵈ .charge c g = refl

proj◦ᶜᵈ : Sealᶜ A ⊸ ◯ᶜ A
proj◦ᶜᵈ .U = ◦
proj◦ᶜᵈ .charge c g = refl

Sealᶜ-open : ⟨ ABS ⟩ → Sealᶜ A ≃ᶜ A
Sealᶜ-open {A} abs = proj◦ᶜᵈ ⨾ᶜ ◯ᶜ-eval-open abs A , equivIsEquiv (Seal-open abs)


infix 1 _⊸ᵈ_
_⊸ᵈ_ : 𝒞 → 𝒞 → 𝒱
A ⊸ᵈ B = A ⊸ Sealᶜ B

glueᵈ : (G : Fractureᶜ) (f• : A ⊸ ⟨ G .A• ⟩ᶜ) (f◦ : A ⊸ ⟨ G .A◦ ⟩ᶜ)
  → ((a : U A) → U (G .α•) (U f• a) ⊑ η• (U f◦ a))
  → A ⊸ fromFractureᵈᶜ G
glueᵈ G f• f◦ f-coh .U a = (f• .U a , f◦ .U a) , f-coh a
glueᵈ G f• f◦ f-coh .charge c a =
  Σ≡Prop (λ _ → thin● ⟨ G .A◦ ⟩ᶜ _ _)
    (ΣPathP (f• .charge c a , f◦ .charge c a))

pairᵈ : (f• : A ⊸ ●ᶜ B) (f◦ : A ⊸ ◯ᶜ B) → ((a : U A) → ●.map η◦ (f• .U a) ⊑ η• (f◦ .U a)) → (A ⊸ᵈ B)
pairᵈ {B = B} = glueᵈ (toFractureᶜ B)

idᵈ : A ⊸ᵈ A
idᵈ .U a = (η• a , η◦ a) , ⊑-refl
idᵈ {A} .charge c a = Σ≡Prop (λ _ → thin● (◯ᶜ A) _ _) refl

⌈_⌉ : (A ⊸ B) → (A ⊸ᵈ B)
⌈ f ⌉ = f ⨾ᶜ idᵈ

infixl 9 _⨾ᵈ_
_⨾ᵈ_ : (A ⊸ᵈ B) → (B ⊸ᵈ C) → (A ⊸ᵈ C)
_⨾ᵈ_ {A} {B} {C} f g =
  pairᵈ
    (f ⨾ᶜ proj•ᶜᵈ ⨾ᶜ g•)
    (f ⨾ᶜ proj◦ᶜᵈ ⨾ᶜ g◦)
    (λ a →
      ⊑-trans (●ᶜ (◯ᶜ C) .is-preorder)
        (bind-coh (• (f .U a)))
        (⊑-mono (●.map (g◦ .U)) (f .U a .snd)))
  where
    g• : ●ᶜ B ⊸ ●ᶜ C
    g• = ●ᶜ.bind (g ⨾ᶜ proj•ᶜᵈ)

    g◦ : ◯ᶜ B ⊸ ◯ᶜ C
    g◦ = ◯ᶜ.bind {B} {C} (g ⨾ᶜ proj◦ᶜᵈ)

    bind-coh : (b• : U (●ᶜ B)) → ●.map η◦ (g• .U b•) ⊑ ●.map (g◦ .U) (●.map η◦ b•)
    bind-coh =
      ●.ind-prop _ (λ _ → thin● (◯ᶜ C) _ _)
        (λ b → g .U b .snd)
        (λ abs → ⊑-reflexive (●.◯-isProp● abs _ _))

squareᵈ : (F G : Fractureᶜ)
  → (f• : ⟨ F .A• ⟩ᶜ ⊸ ⟨ G .A• ⟩ᶜ)
  → (f◦ : ⟨ F .A◦ ⟩ᶜ ⊸ ⟨ G .A◦ ⟩ᶜ)
  → ((a• : U ⟨ F .A• ⟩ᶜ) → U (G .α•) (U f• a•) ⊑ U (●ᶜ.map f◦) (U (F .α•) a•))
  → fromFractureᶜ F ⊸ fromFractureᵈᶜ G
squareᵈ F G f• f◦ f-coh =
  glueᵈ G (proj•ᶜ F ⨾ᶜ f•) (proj◦ᶜ F ⨾ᶜ f◦)
    (λ ((a• , a◦) , acoh) → ⊑∙≡ (f-coh a•) (cong (U (●ᶜ.map f◦)) acoh))

Sealᶜ-fromFracture : (F : Fractureᶜ) → Sealᶜ (fromFractureᶜ F) ≡ fromFractureᵈᶜ F
Sealᶜ-fromFracture F = cong fromFractureᵈᶜ (glue-fracture-sectionᶜ F)

opaque
  unfolding Abstractionᶜ

  squareᵈᶜ : ∀ {A-⊤ A-abs B-⊤ B-abs}
    → (α : A-⊤ ⊸ A-abs) (β : B-⊤ ⊸ B-abs)
    → (f-⊤ : A-⊤ ⊸ B-⊤)
    → (f-abs : A-abs ⊸ B-abs)
    → ((a-⊤ : U A-⊤) → U β (U f-⊤ a-⊤) ⊑ U f-abs (U α a-⊤))
    → Abstractionᶜ A-⊤ A-abs α ⊸ᵈ Abstractionᶜ B-⊤ B-abs β
  squareᵈᶜ {A-⊤} {A-abs} {B-⊤} {B-abs} α β f-⊤ f-abs f-coh =
    subst (Abstractionᶜ A-⊤ A-abs α ⊸_) (sym (Sealᶜ-fromFracture (Abstractionᶜ-Fracture B-⊤ B-abs β)))
      (squareᵈ (Abstractionᶜ-Fracture A-⊤ A-abs α) (Abstractionᶜ-Fracture B-⊤ B-abs β)
        (●ᶜ.map f-⊤) (◯ᶜ.map f-abs)
        (●.ind-prop _ (λ _ → thin● (◯ᶜ B-abs) _ _)
          (λ a → ⊑-mono η• (⊑-mono η◦ (f-coh a)))
          (λ abs → ⊑-reflexive (●.◯-isProp● abs _ _))))
