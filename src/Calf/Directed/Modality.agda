module Calf.Directed.Modality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization as Localization hiding (rec)
open import Cubical.HITs.S1 hiding (rec; elim)
open import Cubical.HITs.Truncation.Properties
  using (isSphereFilled→isOfHLevel)

open import Calf.Core.Interval
open import Calf.Directed.Localization hiding (rec-unique)
open import Calf.Directed.Set
open import Calf.Directed.Thin
open import Calf.Directed.Transitive

private variable X Y Z : Type

data Requirements : Type where
  transitive thin hset : Requirements

opaque
  Sᴾ : Requirements → Type
  Sᴾ transitive = Λ²
  Sᴾ thin = 𝕊 Bool
  Sᴾ hset = S¹

  Tᴾ : Requirements → Type
  Tᴾ transitive = Δ²
  Tᴾ thin = 𝕊 Unit
  Tᴾ hset = Unit

  Fᴾ : (α : Requirements) → Sᴾ α → Tᴾ α
  Fᴾ transitive = ι-horn
  Fᴾ thin = 𝕊-map (terminal Bool)
  Fᴾ hset = terminal S¹

isPreorder : Type → Type
isPreorder = isLocal Fᴾ

∥_∥ᴾ : Type → Type
∥_∥ᴾ = Localize Fᴾ

ηᴾ : X → ∥ X ∥ᴾ
ηᴾ = ∣_∣

isPreorderᴾ : isPreorder ∥ X ∥ᴾ
isPreorderᴾ = isLocal-Localize Fᴾ _

isPropIsPreorder : isProp (isPreorder X)
isPropIsPreorder = isPropΠ (λ _ → isPropIsPathSplitEquiv _)

rec : isPreorder Y → (X → Y) → ∥ X ∥ᴾ → Y
rec = Localization.rec

mapᴾ : (X → Y) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ
mapᴾ f = rec isPreorderᴾ (ηᴾ ∘ f)

map2ᴾ : (X → Y → Z) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ
map2ᴾ f = rec (isLocalΠ λ _ → isPreorderᴾ) (mapᴾ ∘ f)

open isPathSplitEquiv

opaque
  unfolding Fᴾ

  ⊑-trans : isPreorder X → isTransitive X
  ⊑-trans isPreorderX = isPathTransitive→isTransitive (const (isPreorderX transitive))

  isPreorder→isThin : isPreorder X → isThin X
  isPreorder→isThin isPreorderX = transport isBoundarySeparated≡isThin (const (isPreorderX thin))

  isPreorder→isSet : isPreorder X → isSet X
  isPreorder→isSet isPreorderX =
    isSphereFilled→isOfHLevel 1 λ f →
      isPreorderX hset .sec .fst f tt , funExt⁻ (isPreorderX hset .sec .snd f)

  isProp→isPreorder : isProp X → isPreorder X
  isProp→isPreorder =
    isProp→isLocal λ
      { transitive → inl 0𝟚
      ; thin → inr true
      ; hset → base
      }

  isSet∧isThin∧Transitive→isPreorder : isSet X → isThin X → isTransitive X → isPreorder X
  isSet∧isThin∧Transitive→isPreorder setX thinX transX transitive =
    isThin∧isTransitive→isPathTransitive thinX transX _
  isSet∧isThin∧Transitive→isPreorder setX thinX transX thin =
    transport (sym isBoundarySeparated≡isThin) thinX _
  isSet∧isThin∧Transitive→isPreorder setX thinX transX hset =
    fromIsEquiv _
      (compEquiv (UnitToType≃ _) (_ , toIsEquiv _ (transport (sym isS¹Null≡isSet) setX _)) .snd)

isPreorder≡ : isPreorder X ≡ (isSet X × isThin X × isTransitive X)
isPreorder≡ {X} =
  hPropExt isPropIsPreorder
    (isPropΣ isPropIsSet λ _ →
      isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ thinX t t' i a b → thinX _ _ (t a b) (t' a b) i)
    (λ pre → isPreorder→isSet pre , isPreorder→isThin pre , λ {i} {j} {k} → ⊑-trans pre {i} {j} {k})
    (λ (setX , thinX , transX) →
      isSet∧isThin∧Transitive→isPreorder setX thinX (λ {i} {j} {k} → transX {i} {j} {k}))

rec-unique :
  isPreorder Y
  → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≡ g (ηᴾ x))
  → (z : ∥ X ∥ᴾ) → f z ≡ g z
rec-unique = Calf.Directed.Localization.rec-unique

isContrᴾ : (x₀ : X) → ((x : X) → ηᴾ x₀ ≡ ηᴾ x) → isContr ∥ X ∥ᴾ
isContrᴾ x₀ h = ηᴾ x₀ , rec-unique isPreorderᴾ (λ _ → ηᴾ x₀) (λ z → z) h

rec-uniqueP : (P : I → Type) → isPreorder (P i1)
  → (f : ∥ X ∥ᴾ → P i0) (g : ∥ X ∥ᴾ → P i1)
  → ((x : X) → PathP P (f (ηᴾ x)) (g (ηᴾ x)))
  → (z : ∥ X ∥ᴾ) → PathP P (f z) (g z)
rec-uniqueP P isPreorderᴾ₁ f g h z =
  toPathP (rec-unique isPreorderᴾ₁ (transport (λ i → P i) ∘ f) g (λ x → fromPathP (h x)) z)

rec-unique2 :
  isPreorder Z
  → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z)
  → ((x : X) (y : Y) → f (ηᴾ x) (ηᴾ y) ≡ g (ηᴾ x) (ηᴾ y))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → f x y ≡ g x y
rec-unique2 isPreorderZ f g p x y =
  funExt⁻
    (rec-unique (isLocalΠ λ _ → isPreorderZ) f g
      (λ x → funExt (rec-unique isPreorderZ (f (ηᴾ x)) (g (ηᴾ x)) (p x)))
      x)
    y
