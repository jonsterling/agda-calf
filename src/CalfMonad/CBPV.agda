{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV {ℓ ℓ′ M} (monad : Monad {ℓ} {ℓ′} M) where

open Monad monad

open Agda.Primitive
open import Axiom.Extensionality.Propositional         using (Extensionality)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; refl)

tp+ : Set (lsuc ℓ)
tp+ = Set ℓ

record tp- : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    U : Set ℓ′
    bind : {A : tp+} → M A → (A → U) → U

    pure-bind : Extensionality ℓ ℓ′ → ∀ {A} a f → bind {A} (pure a) f ≡ f a
    >>=-bind : Extensionality ℓ ℓ′ → ∀ {A B} e f g → bind {B} (e >>= f) g ≡ bind {A} e λ a → bind (f a) g

open tp- public

F : tp+ → tp-
U (F A) = M A
bind (F B) = _>>=_
pure-bind (F B) ext = pure->>=
>>=-bind (F C) ext = >>=->>=

record _→⁻_ (X Y : tp-) : Set (lsuc ℓ ⊔ ℓ′) where
  field
    _$⁻_ : U X → U Y
    $⁻-bind : ∀ {A} e f → _$⁻_ (bind X {A} e f) ≡ bind Y e λ a → _$⁻_ (f a)

open _→⁻_ public

id⁻ : ∀ {X} → X →⁻ X
id⁻ $⁻ x = x
id⁻ {X} .$⁻-bind e f = refl

open ≡-Reasoning

_∘⁻_ : ∀ {X Y Z} → Y →⁻ Z → X →⁻ Y → X →⁻ Z
(f ∘⁻ g) $⁻ x = f $⁻ (g $⁻ x)
_∘⁻_ {X} {Y} {Z} f g .$⁻-bind e h = begin
  f $⁻ (g $⁻ bind X e h)           ≡⟨ cong (f $⁻_) (g .$⁻-bind e h) ⟩
  f $⁻ (bind Y e (λ a → g $⁻ h a)) ≡⟨ f .$⁻-bind e _ ⟩
  bind Z e (λ a → f $⁻ (g $⁻ h a)) ∎

record _↔⁻_ (X Y : tp-) : Set (lsuc ℓ ⊔ ℓ′) where
  field
    to : X →⁻ Y
    from : Y →⁻ X

    left-inverse-of : ∀ x → from $⁻ (to $⁻ x) ≡ x
    right-inverse-of : ∀ y → to $⁻ (from $⁻ y) ≡ y

module Inverse⁻ where
  open _↔⁻_ public

  id : ∀ {X} → X ↔⁻ X
  id .to = id⁻
  id .from = id⁻
  id .left-inverse-of x = refl
  id .right-inverse-of x = refl

  _∘_ : ∀ {X Y Z} → Y ↔⁻ Z → X ↔⁻ Y → X ↔⁻ Z
  (f ∘ g) .to = f .to ∘⁻ g .to
  (f ∘ g) .from = g .from ∘⁻ f .from
  (f ∘ g) .left-inverse-of x = begin
    g .from $⁻ (f .from $⁻ (f .to $⁻ (g .to $⁻ x))) ≡⟨ cong (g .from $⁻_) (f .left-inverse-of _) ⟩
    g .from $⁻ (g .to $⁻ x)                         ≡⟨ g .left-inverse-of x ⟩
    x                                               ∎
  (f ∘ g) .right-inverse-of z = begin
    f .to $⁻ (g .to $⁻ (g .from $⁻ (f .from $⁻ z))) ≡⟨ cong (f .to $⁻_) (g .right-inverse-of _) ⟩
    f .to $⁻ (f .from $⁻ z)                         ≡⟨ f .right-inverse-of z ⟩
    z                                               ∎
