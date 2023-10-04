{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module Calf.Directed where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

-- Directed ordering on positive types.

infix 4 _≤⁺_
postulate
  _≤⁺_ : val A → val A → □
  ≤⁺-isPreorder : IsPreorder _≡_ (_≤⁺_ {A})

  ≤⁺-mono : (f : val A → val B) →
    f Preserves (_≤⁺_ {A}) ⟶ (_≤⁺_ {B})

≤⁺-reflexive : _≡_ ⇒ _≤⁺_ {A}
≤⁺-reflexive = IsPreorder.reflexive ≤⁺-isPreorder

≤⁺-refl : Reflexive (_≤⁺_ {A})
≤⁺-refl = IsPreorder.refl ≤⁺-isPreorder

≤⁺-trans : Transitive (_≤⁺_ {A})
≤⁺-trans = IsPreorder.trans ≤⁺-isPreorder

≤⁺-syntax : val A → val A → □
≤⁺-syntax {A} = _≤⁺_ {A}

syntax ≤⁺-syntax {A} a a' = a ≤⁺[ A ] a'


-- Directed ordering on negative types.
-- Since `cmp X = val (U X)`, derived form in terms of ordering on positive types.

infix 4 _≤⁻_
_≤⁻_ : cmp X → cmp X → □
_≤⁻_ {X} e e' = e ≤⁺[ U X ] e'

≤⁻-isPreorder : IsPreorder _≡_ (_≤⁻_ {X})
≤⁻-isPreorder {X} =
  record
    { isEquivalence = IsPreorder.isEquivalence (≤⁺-isPreorder {U X})
    ; reflexive = ≤⁺-reflexive
    ; trans = ≤⁺-trans
    }

≤⁻-mono : (f : cmp X → cmp Y) →
  f Preserves (_≤⁻_ {X}) ⟶ (_≤⁻_ {Y})
≤⁻-mono = ≤⁺-mono

postulate
  λ-mono-≤⁻ : {X : val A → tp neg} {f f' : (a : val A) → cmp (X a)}
    → ((a : val A) → _≤⁻_ {X a} (f a) (f' a))
    → _≤⁻_ {Π A X} f f'

≤⁻-reflexive : _≡_ ⇒ _≤⁻_ {X}
≤⁻-reflexive = IsPreorder.reflexive ≤⁻-isPreorder

≤⁻-refl : Reflexive (_≤⁻_ {X})
≤⁻-refl = IsPreorder.refl ≤⁻-isPreorder

≤⁻-trans : Transitive (_≤⁻_ {X})
≤⁻-trans = IsPreorder.trans ≤⁻-isPreorder

≤⁻-syntax : cmp X → cmp X → □
≤⁻-syntax {X} = _≤⁻_ {X}

syntax ≤⁻-syntax {X} e e' = e ≤⁻[ X ] e'


bind-mono-≤⁻ : {A : tp pos} {X : tp neg} {e e' : cmp (F A)} {f f' : val A → cmp X}
  → e ≤⁻[ F A ] e'
  → f ≤⁻[ Π A (λ _ → X) ] f'
  → _≤⁻_ {X} (bind {A} X e f) (bind {A} X e' f')
bind-mono-≤⁻ {A} {X} {e' = e'} {f} {f'} e≤e' f≤f' =
  ≤⁻-trans
    (≤⁻-mono (λ e → bind {A} X e f) e≤e')
    (≤⁻-mono {Π A (λ _ → X)} {X} (bind {A} X e') {f} {f'} f≤f')

bind-monoˡ-≤⁻ : {A : tp pos} {X : tp neg} {e e' : cmp (F A)} (f : val A → cmp X)
  → _≤⁻_ {F A} e e'
  → _≤⁻_ {X} (bind {A} X e f) (bind {A} X e' f)
bind-monoˡ-≤⁻ f e≤e' = bind-mono-≤⁻ e≤e' ≤⁻-refl

bind-monoʳ-≤⁻ : {A : tp pos} {X : tp neg} (e : cmp (F A)) {f f' : val A → cmp X}
  → ((a : val A) → _≤⁻_ {X} (f a) (f' a))
  → _≤⁻_ {X} (bind {A} X e f) (bind {A} X e f')
bind-monoʳ-≤⁻ e f≤f' = bind-mono-≤⁻ (≤⁻-refl {x = e}) (λ-mono-≤⁻ f≤f')


open import Relation.Binary.Structures

module ≤⁻-Reasoning (X : tp neg) where
  open import Relation.Binary.Reasoning.Base.Triple
    (≤⁻-isPreorder {X})
    ≤⁻-trans
    (resp₂ _≤⁻_)
    (λ h → h)
    ≤⁻-trans
    ≤⁻-trans
    public
    hiding (begin-strict_; step-<; step-≈; step-≈˘)
    renaming (step-≤ to step-≤⁻)