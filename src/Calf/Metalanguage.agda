{-# OPTIONS --prop --without-K --rewriting #-}

-- The basic CBPV metalanguage.

open import Calf.CostMonoid

module Calf.Metalanguage where

open import Calf.Prelude
open import Relation.Binary.PropositionalEquality
open import Data.Product

postulate
  mode : □
  pos : mode
  neg : mode

  tp : mode → □
  val : tp pos → □

  F : tp pos → tp neg
  U : tp neg → tp pos

{-# POLARITY val ++ #-}
{-# POLARITY F ++ #-}
{-# POLARITY U ++ #-}

-- This is equivalent to adding "thunk / force" operations. But less bureaucratic.
cmp : tp neg → □
cmp X = val (U X)

postulate
  ret : ∀ {A} → val A → cmp (F A)
  tbind : ∀ {A} → cmp (F A) → (val A → tp neg) → tp neg
  tbind/beta : ∀ {A} {X : val A → tp neg} {v : val A} → tbind (ret v) X ≡ X v
  {-# REWRITE tbind/beta #-}

  dbind : ∀ {A} (X : val A → tp neg) (e : cmp (F A)) (f : (x : val A) → cmp (X x)) → cmp (tbind e X)

  -- note that bind is not a special case of dbind: in general, one does not expect (tbind e (λ _ → m)) ≡ m.
  -- This would hold, however, in the case of a language where there are no true effects. But we don't want
  -- to assume that.
  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X

  bind/beta : ∀ {A X} {v : val A} {f : (x : val A) → cmp X} → bind X (ret v) f ≡ f v
  dbind/beta : ∀ {A} {X : val A → tp neg} {v : val A} {f : (x : val A) → cmp (X x)} → dbind X (ret v) f ≡ f v
  bind/eta : ∀ {A} {e : cmp (F A)} → bind (F A) e ret ≡ e
  {-# REWRITE bind/beta dbind/beta bind/eta #-}

  tbind/assoc : ∀ {A B X} {e : cmp (F A)} {f : val A → cmp (F B)} →
    tbind {B} (bind (F B) e f) X ≡ tbind {A} e (λ v → tbind {B} (f v) X)
  bind/assoc : ∀ {A B C} {e : cmp (F A)} {f1 : val A → cmp (F B)} {f2 : val B → cmp C} →
    bind C (bind (F B) e f1) f2 ≡ bind C e (λ v → bind C (f1 v) f2)
  {-# REWRITE tbind/assoc bind/assoc #-}

  -- dependent product
  Π : (A : tp pos) (X : val A → tp neg) → tp neg
  Π/decode : ∀ {A} {X : val A → tp neg} → val (U (Π A X)) ≡ ((x : val A) → cmp (X x))
  {-# REWRITE Π/decode #-}

  -- mixed polarity dependent sum
  Σ+- : (A : tp pos) (X : val A → tp neg) → tp neg
  Σ+-/decode : ∀ {A} {X : val A → tp neg} → val (U (Σ+- A X)) ≡ Σ (val A) λ x → cmp (X x)
  {-# REWRITE Σ+-/decode #-}

  -- positive dependent sum
  Σ++ : (A : tp pos) (B : val A → tp pos) → tp pos
  Σ++/decode : ∀ {A} {B : val A → tp pos} → val (Σ++ A B) ≡ Σ (val A) λ x → val (B x)
  {-# REWRITE Σ++/decode #-}

  meta⁺ : Set → tp pos
  meta⁺/decode : {A : Set} → val (meta⁺ A) ≡ A
  {-# REWRITE meta⁺/decode #-}

  -- agda sets
  meta : Set → tp neg
  meta/out : ∀ {A} → val (U (meta A)) ≡ A
  {-# REWRITE meta/out #-}

  bind/meta : ∀ A 𝕊 𝕋 e f (g : 𝕊 → 𝕋) → g (bind {A} (meta 𝕊) e f) ≡ bind {A} (meta 𝕋) e (λ a → g(f a))
  tbind/meta : ∀ A 𝕊 e f (p : 𝕊 → □) → p (bind {A} (meta 𝕊) e f) ≡ cmp (tbind {A} e (λ a → meta (p (f a))))
  bind/idem : ∀ A 𝕊 e (f : val A → val A → 𝕊) → bind {A} (meta 𝕊) e (λ a → (bind {A} (meta 𝕊) e (λ a' → f a a'))) ≡ bind {A} (meta 𝕊) e (λ a → f a a)

{-# POLARITY meta ++ #-}


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
