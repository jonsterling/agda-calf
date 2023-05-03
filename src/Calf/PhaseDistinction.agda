{-# OPTIONS --prop --without-K --rewriting #-}

-- The phase distinction for extension.

module Calf.PhaseDistinction where

open import Calf.Prelude
open import Calf.Metalanguage

open import Relation.Binary.PropositionalEquality as P


-- Extensional phase.

postulate
  ext : Ω


-- Open/extensional modality.

◯ : □ → □
◯ A = ext → A

infix 10 ◯⁺_
infix 10 ◯⁻_
postulate
  ext/val : (ext → tp pos) → tp pos
  ext/val/decode : ∀ {A} → val (ext/val A) ≡ ((u : ext) → val (A u))
  {-# REWRITE ext/val/decode #-}

  ext/cmp : (ext → tp neg) → tp neg
  ext/cmp/decode : ∀ {A} → val (U (ext/cmp A)) ≡ ((u : ext) → cmp (A u))
  {-# REWRITE ext/cmp/decode #-}

◯⁺_ : tp pos → tp pos
◯⁺ A = ext/val (λ _ → A)
◯⁻_ : tp neg → tp neg
◯⁻ A = ext/cmp (λ _ → A)


-- Closed/intensional modality.

postulate
  ● : tp pos → tp pos
  η : ∀ {A} → val A → val (● A)
  ∗ : ∀ {A} → ext → val (● A)
  η≡∗ : ∀ {A} (a : val A) u → η {A} a ≡ ∗ u
  ●/ind : ∀ {A} (a : val (● A)) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    ((a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    cmp (X a)
  ●/ind/β₁ : ∀ {A} (a : val A) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    (h : (a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    ●/ind (η a) X x0 x1 h ≡ x0 a
  {-# REWRITE ●/ind/β₁ #-}
  ●/ind/β₂ : ∀ {A} (u : ext) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    (h : (a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    ●/ind (∗ u) X x0 x1 h ≡ x1 u
  {-# REWRITE ●/ind/β₂ #-}


record Extension (X : tp neg) (φ : Ω) (spec : (u : φ) → cmp X) : Set where
  field
    out : cmp X
    law : (u : φ) → out ≡ spec u
open Extension public

witnessed-by : {X : tp neg} {φ : Ω} {out : cmp X} {spec : (u : φ) → cmp X} → ((u : φ) → out ≡ spec u) → Extension X φ spec
witnessed-by {out = out} h = record { out = out ; law = h }

exactly : {X : tp neg} {φ : Ω} {spec : cmp X} → Extension X φ λ _ → spec
exactly {spec = spec} = record { out = spec ; law = λ u → refl }

postulate
  extension-≡ : ∀ {X φ spec} {x y : Extension X φ spec} → out x ≡ out y → x ≡ y
  -- Trivial proof if `law` field is irrelevant. However, this is annoying to
  -- work with, since it requires that further-up proofs be irrelevant.

postulate
  [_∣_↪_] : (X : tp neg) → (φ : Ω) → (spec : (u : φ) → cmp X) → tp neg
  [∣↪]/decode : ∀ {X φ spec} → val (U [ X ∣ φ ↪ spec ]) ≡ Extension X φ spec
  {-# REWRITE [∣↪]/decode #-}
