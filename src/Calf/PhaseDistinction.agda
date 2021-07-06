{-# OPTIONS --prop --without-K --rewriting #-}

-- This file adds the phase distinction for extension.

module Calf.PhaseDistinction where

open import Calf.Prelude
open import Calf.Metalanguage

open import Relation.Binary.PropositionalEquality as P


-- Extensional open.

postulate
  ext : Ω


-- Open modality.

◯ : □ → □
◯ A = ext → A

infix 10 ◯⁺_
infix 10 ◯⁻_
postulate
  ext/val : (ext → tp pos) → tp pos
  ext/val/decode : ∀ {A} → val (ext/val A) ≡ ∀ (u : ext) → (val (A u))
  {-# REWRITE ext/val/decode #-}

  ext/cmp : (ext → tp neg) → tp neg
  ext/cmp/decode : ∀ {A} → val (U (ext/cmp A)) ≡ ∀ (u : ext) → (cmp (A u))
  {-# REWRITE ext/cmp/decode #-}

◯⁺_ : tp pos → tp pos
◯⁺ A = ext/val (λ _ → A)
◯⁻_ : tp neg → tp neg
◯⁻ A = ext/cmp (λ _ → A)


-- Closed modality.

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
