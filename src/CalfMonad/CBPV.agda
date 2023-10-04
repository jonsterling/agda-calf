{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV {ℓ ℓ′ M} (monad : Monad {ℓ} {ℓ′} M) where

open Monad monad

open Agda.Primitive
open import Data.Empty.Polymorphic                     using (⊥; ⊥-elim)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base                 using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; cong₂; refl)

tp+ : Set (lsuc ℓ)
tp+ = Set ℓ

record tp- : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    U : Set ℓ′
    bind : {A : tp+} → M A → (A → U) → U

    pure-bind : ∀ {A} a f → bind {A} (pure a) f ≡ f a
    >>=-bind : ∀ {A B} e f g → bind {B} (e >>= f) g ≡ bind {A} e λ a → bind (f a) g

open tp- public

F : tp+ → tp-
U (F A) = M A
bind (F B) = _>>=_
pure-bind (F B) = pure->>=
>>=-bind (F C) = >>=->>=

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
_∘⁻_ {X} {Y} {Z} f g .$⁻-bind e h =
  f $⁻ (g $⁻ bind X e h)           ≡⟨ cong (f $⁻_) (g .$⁻-bind e h) ⟩
  f $⁻ (bind Y e (λ a → g $⁻ h a)) ≡⟨ f .$⁻-bind e _ ⟩
  bind Z e (λ a → f $⁻ (g $⁻ h a)) ∎

map : ∀ {A B} → (A → B) → F A →⁻ F B
map f $⁻ e = e >>= λ a → pure (f a)
map f .$⁻-bind e g = >>=->>= e g _

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
  (f ∘ g) .left-inverse-of x =
    g .from $⁻ (f .from $⁻ (f .to $⁻ (g .to $⁻ x))) ≡⟨ cong (g .from $⁻_) (f .left-inverse-of _) ⟩
    g .from $⁻ (g .to $⁻ x)                         ≡⟨ g .left-inverse-of x ⟩
    x                                               ∎
  (f ∘ g) .right-inverse-of z =
    f .to $⁻ (g .to $⁻ (g .from $⁻ (f .from $⁻ z))) ≡⟨ cong (f .to $⁻_) (g .right-inverse-of _) ⟩
    f .to $⁻ (f .from $⁻ z)                         ≡⟨ f .right-inverse-of z ⟩
    z                                               ∎

⊤⁻ : tp-
U ⊤⁻ = ⊤
bind ⊤⁻ = _
pure-bind ⊤⁻ a f = refl
>>=-bind ⊤⁻ e f g = refl

_→⁻⊤⁻ : ∀ X → X →⁻ ⊤⁻
(X →⁻⊤⁻) $⁻ x = _
(X →⁻⊤⁻) .$⁻-bind e f = refl

⊥⁻ : tp-
⊥⁻ = F ⊥

⊥⁻→⁻_ : ∀ X → ⊥⁻ →⁻ X
(⊥⁻→⁻ X) $⁻ e = bind X e ⊥-elim
(⊥⁻→⁻ X) .$⁻-bind e f = >>=-bind X e f ⊥-elim

_×⁻_ : tp- → tp- → tp-
U (X ×⁻ Y) = U X × U Y
bind (X ×⁻ Y) e f = bind X e (λ a → proj₁ (f a)) , bind Y e (λ a → proj₂ (f a))
pure-bind (X ×⁻ Y) a f = cong₂ _,_ (pure-bind X a _) (pure-bind Y a _)
>>=-bind (X ×⁻ Y) e f g = cong₂ _,_ (>>=-bind X e f _) (>>=-bind Y e f _)

proj₁⁻ : ∀ {X Y} → (X ×⁻ Y) →⁻ X
proj₁⁻ ._$⁻_ = proj₁
proj₁⁻ .$⁻-bind e f = refl

proj₂⁻ : ∀ {X Y} → (X ×⁻ Y) →⁻ Y
proj₂⁻ ._$⁻_ = proj₂
proj₂⁻ .$⁻-bind e f = refl

⟨_,⁻_⟩ : ∀ {X Y Z} → Z →⁻ X → Z →⁻ Y → Z →⁻ (X ×⁻ Y)
⟨ f ,⁻ g ⟩ $⁻ z = f $⁻ z , g $⁻ z
⟨ f ,⁻ g ⟩ .$⁻-bind e h = cong₂ _,_ (f .$⁻-bind e h) (g .$⁻-bind e h)
