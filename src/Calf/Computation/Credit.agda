module Calf.Computation.Credit where

open import Cubical.Foundations.Path using (fromPathP⁻)
open import Cubical.Foundations.Transport using (transport⁻-fillerExt⁻)
open import Cubical.Foundations.Univalence using (ua)

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Closed as ●ᶜ
open import Calf.Computation.Glue hiding (squareᶜ)
open import Calf.Computation.Open as ◯ᶜ
open import Calf.Computation.Seal

open Fractureᶜ

opaque
  ▷[_]_ : ℂ → 𝒞 → 𝒞
  ▷[ c ] A = Abstractionᶜ A A (chargeᶜ c)

  ▷-map : (A ⊸ B) → (▷[ c ] A ⊸ ▷[ c ] B)
  ▷-map {A} {B} {c} f =
    squareᶜ (chargeᶜ c) (chargeᶜ c)
      f
      f
      (sym ∘ f .charge c)

  ▷-mapᵈ : (A ⊸ᵈ B) → (▷[ c ] A ⊸ᵈ ▷[ c ] B)
  ▷-mapᵈ f = {!   !}

  ▷-0 : ▷[ 0ℂ ] A ≡ A
  ▷-0 {A} = cong (Abstractionᶜ A A) chargeᶜ-0 ∙ Abstractionᶜ-id A

  ▷-+ : ▷[ c₁ +ℂ c₂ ] A ≡ ▷[ c₁ ] ▷[ c₂ ] A
  ▷-+ {c₁} {c₂} {A} =
      ▷[ c₁ +ℂ c₂ ] A
    ≡⟨⟩
      Abstractionᶜ A A (chargeᶜ (c₁ +ℂ c₂))
    ≡⟨ cong (Abstractionᶜ A A) (chargeᶜ-+ c₁ c₂) ⟩
      Abstractionᶜ A A (chargeᶜ c₂ ⨾ᶜ chargeᶜ c₁)
    ≡⟨ sym
        (Abstractionᶜ-fuse
          (chargeᶜ c₂) (chargeᶜ c₂)
          (chargeᶜ c₁) (chargeᶜ c₁)
          (λ a → cong ((_$ a) ∘ U) (chargeᶜ-comm {A} c₁ c₂)))
    ⟩
      Abstractionᶜ
        (Abstractionᶜ A A (chargeᶜ c₂))
        (Abstractionᶜ A A (chargeᶜ c₂))
        (squareᶜ (chargeᶜ c₂) (chargeᶜ c₂) (chargeᶜ c₁) (chargeᶜ c₁) λ a → cong ((_$ a) ∘ U) (chargeᶜ-comm {A} c₁ c₂))
    ≡⟨
      cong
        (Abstractionᶜ (Abstractionᶜ A A (chargeᶜ c₂)) (Abstractionᶜ A A (chargeᶜ c₂)))
        (squareᶜ-charge (chargeᶜ c₂) c₁ λ a → cong ((_$ a) ∘ U) (chargeᶜ-comm {A} c₁ c₂))
    ⟩
      Abstractionᶜ (Abstractionᶜ A A (chargeᶜ c₂)) (Abstractionᶜ A A (chargeᶜ c₂)) (chargeᶜ c₁)
    ≡⟨⟩
      ▷[ c₁ ] (▷[ c₂ ] A)
    ∎

  ▷-Fracture : ℂ → 𝒞 → Fractureᶜ
  ▷-Fracture c A .A• = ●ᶜ• A
  ▷-Fracture c A .A◦ = ◯ᶜ◦ A
  ▷-Fracture c A .α• = ●ᶜ.map (chargeᶜ c ⨾ᶜ η◦ᶜ)

  ▷-open : ⟨ ABS ⟩ → (c : ℂ) (A : 𝒞) → ▷[ c ] A ≡ A
  ▷-open abs c A = Abstractionᶜ-open (chargeᶜ c) abs

  ▷-●ᶜ : (c : ℂ) (A : 𝒞) → ●ᶜ (▷[ c ] A) ≡ ●ᶜ A
  ▷-●ᶜ c A = ●ᶜ-Abstractionᶜ (chargeᶜ c)

  ▷-◯ᶜ : (c : ℂ) (A : 𝒞) → ◯ᶜ (▷[ c ] A) ≡ ◯ᶜ A
  ▷-◯ᶜ c A = ◯ᶜ-Abstractionᶜ (chargeᶜ c)

  ▷-coherence : (c : ℂ) (A : 𝒞) →
    PathP
      (λ i → sym (▷-●ᶜ c A) i ⊸ ●ᶜ (sym (▷-◯ᶜ c A) i))
      (●ᶜ.map (chargeᶜ c ⨾ᶜ η◦ᶜ {A = A}))
      (●ᶜ.map (η◦ᶜ {A = ▷[ c ] A}))
  ▷-coherence c A =
    Abstractionᶜ-coherence (chargeᶜ c)

  waste-all : (c : ℂ) → ▷[ c ] A ⊸ᵈ A
  waste-all {A} c =
    subst (▷[ c ] A ⊸ᵈ_) (Abstractionᶜ-id A) $
    squareᵈᶜ (chargeᶜ c) idᶜ idᶜ idᶜ λ _ →
    ≡∙⊑ (sym (A .charge-0)) (⊑-mono (flip (A .charge) _) (0⊑c c))

  waste : (A : 𝒞) {c c' : ℂ} → c ⊑ c' → ▷[ c' ] A ⊸ᵈ ▷[ c ] A
  waste A {c} {c'} c⊑c' =
    subst (λ c'' → ▷[ c'' ] A ⊸ᵈ ▷[ c ] A) todo $
    subst (_⊸ᵈ ▷[ c ] A) (sym ▷-+) $
    ▷-mapᵈ (waste-all c'∸c)
    where
      c'∸c : ℂ
      c'∸c = {!   !}

      todo : c +ℂ c'∸c ≡ c'
      todo = {!   !}

  save : (A : 𝒞) (c : ℂ) → A ⊸ ▷[ c ] A
  save A c = triangle-⊤ (chargeᶜ c) idᶜ

  spend : (A : 𝒞) (c : ℂ) → ▷[ c ] A ⊸ A
  spend A c = triangle-abs idᶜ

  save⨾spend≡chargeᶜ : (A : 𝒞) (c : ℂ) → save A c ⨾ᶜ spend A c ≡ chargeᶜ c
  save⨾spend≡chargeᶜ A c =
      save A c ⨾ᶜ spend A c
    ≡⟨ cong (_⨾ᶜ spend A c) (⨾ᶜ-identityˡ (triangleᶜ (chargeᶜ c))) ⟩
      triangleᶜ (chargeᶜ c) ⨾ᶜ spend A c
    ≡⟨ sym (fromPathP (λ i → triangleᶜ (chargeᶜ c) ⨾ᶜ spend-path i)) ⟩
      transport (λ i → A ⊸ Abstractionᶜ-id A i) (triangleᶜ (chargeᶜ c) ⨾ᶜ SQ₂)
    ≡⟨ cong (transport (λ i → A ⊸ Abstractionᶜ-id A i)) lemma ⟩
      transport (λ i → A ⊸ Abstractionᶜ-id A i) (chargeᶜ c ⨾ᶜ triangleᶜ idᶜ)
    ≡⟨ fromPathP (λ i → chargeᶜ {A} c ⨾ᶜ triangleᶜ-id i) ⟩
      chargeᶜ c ⨾ᶜ idᶜ
    ≡⟨ ⨾ᶜ-identityʳ (chargeᶜ c) ⟩
      chargeᶜ c
    ∎
    where
      SQ₂ : Abstractionᶜ A A (chargeᶜ c) ⊸ Abstractionᶜ A A idᶜ
      SQ₂ = squareᶜ (chargeᶜ c) idᶜ (chargeᶜ c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)

      spend-path : PathP (λ i → Abstractionᶜ A A (chargeᶜ c) ⊸ Abstractionᶜ-id A i) SQ₂ (spend A c)
      spend-path = transport-filler (λ i → Abstractionᶜ A A (chargeᶜ c) ⊸ Abstractionᶜ-id A i) SQ₂

      lemma : triangleᶜ (chargeᶜ c) ⨾ᶜ SQ₂ ≡ chargeᶜ c ⨾ᶜ triangleᶜ idᶜ
      lemma =
          triangleᶜ-natural (chargeᶜ c ⨾ᶜ idᶜ) idᶜ (λ _ → refl)
        ∙ cong (_⨾ᶜ triangleᶜ idᶜ) (⨾ᶜ-identityʳ (chargeᶜ c))
