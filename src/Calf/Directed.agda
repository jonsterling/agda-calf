{-# OPTIONS --rewriting #-}

module Calf.Directed where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality

open import Relation.Binary.Core
open import Relation.Binary.Definitions

infix 4 _≲_
postulate
  _≲_ : {X : tp neg} → cmp X → cmp X → □

  ≲-refl : {X : tp neg} → Reflexive (_≲_ {X})
  ≲-trans : {X : tp neg} → Transitive (_≲_ {X})

  ≲-mono : {X Y : tp neg} (f : cmp X → cmp Y) →
    f Preserves (_≲_ {X}) ⟶ (_≲_ {Y})

  λ-mono-≲ : {A : tp pos} {X : val A → tp neg} {f₁ f₂ : (a : val A) → cmp (X a)}
    → ((a : val A) → _≲_ {X a} (f₁ a) (f₂ a))
    → _≲_ {Π A X} f₁ f₂

≲-reflexive : {X : tp neg} → _≡_ ⇒ _≲_ {X}
≲-reflexive refl = ≲-refl

≲-syntax : {X : tp neg} → cmp X → cmp X → □
≲-syntax {X} = _≲_ {X}

syntax ≲-syntax {X} e₁ e₂ = e₁ ≲[ X ] e₂

bind-mono-≲ : {A : tp pos} {X : tp neg} {e₁ e₂ : cmp (F A)} {f₁ f₂ : val A → cmp X}
  → _≲_ {F A} e₁ e₂
  → ((a : val A) → _≲_ {X} (f₁ a) (f₂ a))
  → _≲_ {X} (bind {A} X e₁ f₁) (bind {A} X e₂ f₂)
bind-mono-≲ {A} {X} {e₂ = e₂} {f₁ = f₁} {f₂} e₁≲e₂ f₁≲f₂ =
  ≲-trans
    (≲-mono (λ e → bind {A} X e f₁) e₁≲e₂)
    (≲-mono {Π A (λ _ → X)} {X} (bind {A} X e₂) {f₁} {f₂} (λ-mono-≲ f₁≲f₂))

bind-monoˡ-≲ : {A : tp pos} {X : tp neg} {e₁ e₂ : cmp (F A)} (f : val A → cmp X)
  → _≲_ {F A} e₁ e₂
  → _≲_ {X} (bind {A} X e₁ f) (bind {A} X e₂ f)
bind-monoˡ-≲ f e₁≲e₂ = bind-mono-≲ e₁≲e₂ (λ a → ≲-refl)

bind-monoʳ-≲ : {A : tp pos} {X : tp neg} (e : cmp (F A)) {f₁ f₂ : val A → cmp X}
  → ((a : val A) → _≲_ {X} (f₁ a) (f₂ a))
  → _≲_ {X} (bind {A} X e f₁) (bind {A} X e f₂)
bind-monoʳ-≲ e f₁≲f₂ = bind-mono-≲ (≲-refl {x = e}) f₁≲f₂


open import Relation.Binary.Structures

≲-isPreorder : {X : tp neg} → IsPreorder _≡_ (_≲_ {X})
≲-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = λ { refl → ≲-refl }
  ; trans         = ≲-trans
  }

module ≲-Reasoning (X : tp neg) where
  open import Function
  open import Relation.Binary.Reasoning.Base.Triple
    (≲-isPreorder {X})
    ≲-trans
    (resp₂ _≲_)
    id
    ≲-trans
    ≲-trans
    public
    hiding (begin-strict_; step-<; step-≈; step-≈˘)
    renaming (step-≤ to step-≲)

open ≲-Reasoning
