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

≤⁺-mono₂ : (f : val A → val B → val C) →
  f Preserves₂ (_≤⁺_ {A}) ⟶ (_≤⁺_ {B}) ⟶ (_≤⁺_ {C})
≤⁺-mono₂ f a≤a' b≤b' =
  ≤⁺-trans
  (≤⁺-mono (f _) b≤b')
  (≤⁺-mono (λ a → f a _) a≤a')

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

≤⁻-mono₂ : (f : cmp X → cmp Y → cmp Z) →
  f Preserves₂ (_≤⁻_ {X}) ⟶ (_≤⁻_ {Y}) ⟶ (_≤⁻_ {Z})
≤⁻-mono₂ = ≤⁺-mono₂

postulate
  λ-mono-≤⁻ : {X : val A → tp⁻} {f f' : (a : val A) → cmp (X a)}
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


bind-mono-≤⁻ : {e e' : cmp (F A)} {f f' : val A → cmp X}
  → e ≤⁻[ F A ] e'
  → f ≤⁻[ Π A (λ _ → X) ] f'
  → (bind {A} X e f) ≤⁻[ X ] (bind {A} X e' f')
bind-mono-≤⁻ {A} {X} {e' = e'} {f} {f'} e≤e' f≤f' =
  ≤⁻-trans
    (≤⁻-mono (λ e → bind {A} X e f) e≤e')
    (≤⁻-mono {Π A (λ _ → X)} {X} (bind {A} X e') {f} {f'} f≤f')

bind-monoˡ-≤⁻ : {e e' : cmp (F A)} (f : val A → cmp X)
  → e ≤⁻[ F A ] e'
  → (bind {A} X e f) ≤⁻[ X ] (bind {A} X e' f)
bind-monoˡ-≤⁻ f e≤e' = bind-mono-≤⁻ e≤e' ≤⁻-refl

bind-monoʳ-≤⁻ : (e : cmp (F A)) {f f' : val A → cmp X}
  → ((a : val A) → (f a) ≤⁻[ X ] (f' a))
  → (bind {A} X e f) ≤⁻[ X ] (bind {A} X e f')
bind-monoʳ-≤⁻ e f≤f' = bind-mono-≤⁻ (≤⁻-refl {x = e}) (λ-mono-≤⁻ f≤f')

bind-irr-mono-≤⁻ : {e₁ e₁' : cmp (F A)} {e₂ e₂' : cmp X}
  → e₁ ≤⁻[ F A ] e₁'
  → e₂ ≤⁻[ X ] e₂'
  → (bind {A} X e₁ λ _ → e₂) ≤⁻[ X ] (bind {A} X e₁' λ _ → e₂')
bind-irr-mono-≤⁻ e₁≤e₁' e₂≤e₂' =
  bind-mono-≤⁻ e₁≤e₁' (λ-mono-≤⁻ λ a → e₂≤e₂')

bind-irr-monoˡ-≤⁻ : {e₁ e₁' : cmp (F A)} {e₂ : cmp X}
  → e₁ ≤⁻[ F A ] e₁'
  → (bind {A} X e₁ λ _ → e₂) ≤⁻[ X ] (bind {A} X e₁' λ _ → e₂)
bind-irr-monoˡ-≤⁻ e₁≤e₁' =
  bind-irr-mono-≤⁻ e₁≤e₁' ≤⁻-refl


open import Level using (0ℓ)
open import Relation.Binary using (Preorder)
open import Relation.Binary.Structures

≤⁻-preorder : tp⁻ → Preorder 0ℓ 0ℓ 0ℓ
Preorder.Carrier (≤⁻-preorder X) = cmp X
Preorder._≈_ (≤⁻-preorder X) = _≡_
Preorder._≲_ (≤⁻-preorder X) = _≤⁻_ {X}
Preorder.isPreorder (≤⁻-preorder X) = ≤⁻-isPreorder {X}

module ≤⁻-Reasoning (X : tp⁻) where
  open import Relation.Binary.Reasoning.Preorder (≤⁻-preorder X) public
