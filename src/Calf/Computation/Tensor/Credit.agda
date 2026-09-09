module Calf.Computation.Tensor.Credit where

open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Core.Abstract using (ABS)
open import Calf.Core.Cost
open import Calf.Value
import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Credit
open import Calf.Computation.Glue hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Power using (Πᶜ)

open import Calf.Computation.Tensor.Base
open import Calf.Computation.Tensor.Closed

open Fractureᶜ

opaque
  unfolding Abstractionᶜ triangleᶜ

  ⊗-Abstractionᶜ : (A : 𝒞) {B-⊤ B-abs : 𝒞} {β : B-⊤ ⊸ B-abs}
    → A ⊗ Abstractionᶜ B-⊤ B-abs β ≡ Abstractionᶜ (A ⊗ B-⊤) (A ⊗ B-abs) (map₂ idᶜ β)
  ⊗-Abstractionᶜ A {B-⊤} {B-abs} {β} =
    sym (glue-fracture-retractᶜ _) ∙ cong fromFractureᶜ (sym fracture-proof)
    where
      fwd : ●ᶜ (A ⊗ B-⊤) ⊸ ●ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      fwd = ●ᶜ.map (map₂ idᶜ (triangleᶜ β))

      fwd-equiv : isEquiv (fwd .U)
      fwd-equiv = ●ᶜ-map₂-equiv (●ᶜ.map-id-equiv {A}) (●ᶜ-Abstractionᶜ-≃ᶜ β .snd)

      q• : ●ᶜ (A ⊗ B-⊤) ≡ ●ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      q• = conservativity fwd fwd-equiv

      q◦ : ◯ᶜ (A ⊗ B-abs) ≡ ◯ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      q◦ =
        cong (Πᶜ ⟨ ABS ⟩)
          (funExt λ abs → sym (cong (A ⊗_) (Abstractionᶜ-open β abs)))

      qα :
        PathP (λ i → q• i ⊸ ●ᶜ (q◦ i))
          (●ᶜ.map (map₂ idᶜ β ⨾ᶜ η◦ᶜ))
          (●ᶜ.map η◦ᶜ)
      qα =
        ⊸-path q• (cong ●ᶜ q◦)
          (ua→ {e = fwd .U , fwd-equiv}
            (●.elim (λ _ → ●.isModalPathP ●.isModal●) λ w →
              rec-uniqueP (λ i → U (●ᶜ (q◦ i)))
                (●ᶜ (◯ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)) .is-preorder)
                (λ w → ●.η• ((map₂ idᶜ β ⨾ᶜ η◦ᶜ) .U w))
                (λ w → ●.η• (η◦ᶜ {A = A ⊗ Abstractionᶜ B-⊤ B-abs β} .U
                  (map₂ idᶜ (triangleᶜ β) .U w)))
                (⊗₀-elimProp {A} {B-⊤}
                  (λ _ → isOfHLevelPathP' {A = λ i → U (●ᶜ (q◦ i))} 1
                    (is-set (●ᶜ (◯ᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)))) _ _)
                  (λ a b →
                    congP (λ _ → ●.η•) (funExt λ abs →
                      congP (λ i q → ηᴾ (inj {A} {Abstractionᶜ-open β abs (~ i)} a q))
                        (symP (triangle-U-openP β b (β .U b) refl abs)))))
                w))

      fracture-proof :
        Abstractionᶜ-Fracture (A ⊗ B-⊤) (A ⊗ B-abs) (map₂ idᶜ β)
          ≡ toFractureᶜ (A ⊗ Abstractionᶜ B-⊤ B-abs β)
      fracture-proof = Fractureᶜ-path-U q• q◦ qα

▷⊤-rec : U A → ▷[ 0ℂ ] ⊤ ⊸ A
▷⊤-rec {A} a = subst (_⊸ A) (sym ▷-0) (⊤-rec a)

map₂-idᶜ-chargeᶜ : ∀ c → map₂ (idᶜ {A}) (chargeᶜ {B} c) ≡ chargeᶜ {A ⊗ B} c
map₂-idᶜ-chargeᶜ c =
  ⊸-path refl refl (funExt (⊗₀-rec-unique isPreorderᴾ _ _ λ a b → sym (∥-slide c a b)))

opaque
  unfolding ▷[_]_

  ⊗-▷-distribʳ : ∀ c → (A ⊗ ▷[ c ] B) ≡ (▷[ c ] (A ⊗ B))
  ⊗-▷-distribʳ {A} {B} c =
    ⊗-Abstractionᶜ A ∙ cong (Abstractionᶜ (A ⊗ B) (A ⊗ B)) (map₂-idᶜ-chargeᶜ c)

  ⊗-▷-distribˡ : ∀ c → (▷[ c ] A ⊗ B) ≡ (▷[ c ] (A ⊗ B))
  ⊗-▷-distribˡ c = ⊗-comm ∙ ⊗-▷-distribʳ c ∙ cong (▷[ c ]_) ⊗-comm

opaque
  ▷-⊗ : ∀ c₁ c₂ → ((▷[ c₁ ] ⊤) ⊗ (▷[ c₂ ] ⊤)) ≡ ▷[ c₁ +ℂ c₂ ] ⊤
  ▷-⊗ c₁ c₂ = ⊗-▷-distribˡ c₁ ∙ cong (▷[ c₁ ]_) ⊗-identityˡ ∙ sym ▷-+
