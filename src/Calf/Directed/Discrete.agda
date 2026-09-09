module Calf.Directed.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization

open import Calf.Core.Interval
open import Calf.Directed.Modality
open import Calf.Directed.Path
open import Calf.Directed.Thin
open import Calf.Directed.Transitive

private variable X Y : Type

isDiscrete : Type → Type
isDiscrete X = isLocal {A = Unit} (λ _ → terminal 𝟚) X

isDiscrete→isEquiv[⊑-reflexive] : isDiscrete X → {x x' : X} → isEquiv (⊑-reflexive {X} {x} {x'})
isDiscrete→isEquiv[⊑-reflexive] {X} isDiscreteX {x} {x'} = equivIsEquiv ≡≃⊑
  where
    discreteness : X ≃ (𝟚 → X)
    discreteness = compEquiv (invEquiv (UnitToType≃ X)) (_ , toIsEquiv _ (isDiscreteX tt))

    isContrP : isContr (Σ[ p ∈ (𝟚 → X) ] (x ≡ p 0𝟚))
    isContrP = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-fst discreteness) (isContrSingl x)

    ⊑≃Σ : (x ⊑ x') ≃ (Σ[ p ∈ (𝟚 → X) ] ((x ≡ p 0𝟚) × (p 1𝟚 ≡ x')))
    ⊑≃Σ =
      isoToEquiv $
      iso
        (λ q → path q , sym (path₀ q) , path₁ q)
        (λ (p , p₀ , p₁) → p , sym p₀ , p₁)
        (λ _ → refl)
        (λ _ → refl)

    ≡≃⊑ : (x ≡ x') ≃ (x ⊑ x')
    ≡≃⊑ =
      compEquiv (invEquiv (Σ-contractFst isContrP)) $
      compEquiv Σ-assoc-≃ $
      invEquiv ⊑≃Σ

isSet∧isDiscrete→isThin : isSet X → isDiscrete X → isThin X
isSet∧isDiscrete→isThin isSetX isDiscreteX x x' =
  isOfHLevelRespectEquiv 1 (⊑-reflexive , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX) (isSetX x x')

opaque
  isSet∧isDiscrete→isPreorder : isSet X → isDiscrete X → isPreorder X
  isSet∧isDiscrete→isPreorder {X} isSetX isDiscreteX =
    isSet∧isThin∧Transitive→isPreorder isSetX (isSet∧isDiscrete→isThin isSetX isDiscreteX)
      λ x⊑x' x'⊑x'' → ⊑-reflexive (⊑⇒≡ x⊑x' ∙ ⊑⇒≡ x'⊑x'')
    where
      ⊑⇒≡ : {x x' : X} → x ⊑ x' → x ≡ x'
      ⊑⇒≡ = invEq (⊑-reflexive , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX)

isEquivEv→isEquivConst : (y₀ : Y)
  → isEquiv (λ (f : Y → X) → f y₀) → isEquiv (const {A = X} {B = Y})
isEquivEv→isEquivConst k₀ = composesToId→Equiv _ const refl

isLocalTerminal→isEquivConst : {A : Type} {S : A → Type}
  → isLocal (λ α → terminal (S α)) X → (α : A) → isEquiv (const {A = X} {B = S α})
isLocalTerminal→isEquivConst l α =
  equivIsEquiv (compEquiv (invEquiv (UnitToType≃ _)) (_ , toIsEquiv _ (l α)))

isEquivConst→isLocalTerminal : {A : Type} {S : A → Type}
  → ((α : A) → isEquiv (const {A = X} {B = S α})) → isLocal (λ α → terminal (S α)) X
isEquivConst→isLocalTerminal e α = fromIsEquiv _ (compEquiv (UnitToType≃ _) (_ , e α) .snd)

null[Unit] : isEquiv (const {A = X} {B = Unit})
null[Unit] {X} = isEquivEv→isEquivConst tt (equivIsEquiv (UnitToType≃ X))

null[𝟚] : isDiscrete X → isEquiv (const {A = X} {B = 𝟚})
null[𝟚] isDiscreteX = isLocalTerminal→isEquivConst isDiscreteX tt

null[Λ²] : isDiscrete X → isEquiv (const {A = X} {B = Λ²})
null[Λ²] {X} isDiscreteX =
  isEquivEv→isEquivConst (inl 0𝟚) (precomposesToId→Equiv _ (chain .fst) refl (chain .snd))
  where
    constₚ : X ≃ (𝟚 → X)
    constₚ = const , null[𝟚] isDiscreteX

    chain : X ≃ (Λ² → X)
    chain =
        X
      ≃⟨ invEquiv (Σ-contractSnd λ _ → isContrSingl _) ⟩
        Σ[ a ∈ X ] Σ[ b ∈ X ] (a ≡ b)
      ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-cong-equiv-fst constₚ) ⟩
        Σ[ a ∈ X ] Σ[ q ∈ (𝟚 → X) ] (a ≡ q 0𝟚)
      ≃⟨ Σ-cong-equiv-fst constₚ ⟩
        Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚)
      ≃⟨ isoToEquiv (invIso Λ²-elim) ⟩
        (Λ² → X)
      ■

null[𝕊Unit] : isDiscrete X → isEquiv (const {A = X} {B = 𝕊 Unit})
null[𝕊Unit] {X} isDiscreteX =
  isEquivEv→isEquivConst (inr false) (precomposesToId→Equiv _ (chain .fst) refl (chain .snd))
  where
    chain : X ≃ (𝕊 Unit → X)
    chain =
        X
      ≃⟨ invEquiv (compEquiv Σ-assoc-≃ (Σ-contractSnd λ _ → isContrSingl _)) ⟩
        Σ[ p ∈ X × X ] (fst p ≡ snd p)
      ≃⟨ Σ-cong-equiv-snd (λ _ → ⊑-reflexive , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX) ⟩
        Σ[ p ∈ X × X ] (fst p ⊑ snd p)
      ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv (UnitToType≃ _)) ⟩
        Σ[ p ∈ X × X ] (Unit → fst p ⊑ snd p)
      ≃⟨ isoToEquiv (invIso (𝕊-elim Unit)) ⟩
        (𝕊 Unit → X)
      ■

null[Δ²] : isSet X → isDiscrete X → isEquiv (const {A = X} {B = Δ²})
null[Δ²] {X} isSetX isDiscreteX =
  isEquivEv→isEquivConst (inl (inl 0𝟚)) (precomposesToId→Equiv _ (chain .fst) refl (chain .snd))
  where
    contr⊑ : (x : X) → isContr (x ⊑ x)
    contr⊑ x =
      isOfHLevelRespectEquiv 0
        (⊑-reflexive , isDiscrete→isEquiv[⊑-reflexive] isDiscreteX)
        (refl , isSetX x x refl)

    chain : X ≃ (Δ² → X)
    chain =
        X
      ≃⟨ invEquiv (Σ-contractSnd contr⊑) ⟩
        Σ[ x ∈ X ] (x ⊑ x)
      ≃⟨ Σ-cong-equiv-fst (const , null[Λ²] isDiscreteX) ⟩
        Σ[ h ∈ (Λ² → X) ] (h (inl 0𝟚) ⊑ h (inr 1𝟚))
      ≃⟨ isoToEquiv (invIso Δ²-elim) ⟩
        (Δ² → X)
      ■

opaque
  unfolding Fᴾ

  isSet∧isDiscrete→nullᴾ : isSet X → isDiscrete X
    → (α : Requirements) → isEquiv (const {A = X} {B = Tᴾ α})
  isSet∧isDiscrete→nullᴾ isSetX isDiscreteX transitive = null[Δ²] isSetX isDiscreteX
  isSet∧isDiscrete→nullᴾ isSetX isDiscreteX thin = null[𝕊Unit] isDiscreteX
  isSet∧isDiscrete→nullᴾ isSetX isDiscreteX hset = null[Unit]
