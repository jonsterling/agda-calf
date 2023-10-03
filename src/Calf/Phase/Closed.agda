{-# OPTIONS --rewriting #-}

-- Closed/intensional modality.

module Calf.Phase.Closed where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Calf.Phase.Core


-- data ● (A : tp pos) : tp pos where
--   η : A → ● A
--   ∗ : ext → ● A
--   η≡∗ : (a : A) (u : ext) → η a ≡ ∗ u

postulate
  ● : tp pos → tp pos

  η : val A → val (● A)
  ∗ : ext → val (● A)
  η≡∗ : (a : val A) (u : ext) → η {A} a ≡ ∗ u
  η≡∗/uni : {x x' : val (● A)} (p p' : x ≡ x') → p ≡ p'

  ●/ind : (a : val (● A)) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    ((a : val A) → (u : ext) → subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u) →
    cmp (X a)

  ●/ind/β₁ : (a : val A) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    (h : (a : val A) → (u : ext) → subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    ●/ind (η a) X x0 x1 h ≡ x0 a
  {-# REWRITE ●/ind/β₁ #-}
  ●/ind/β₂ : (u : ext) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (∗ u))) →
    (h : (a : val A) → (u : ext) → subst (λ a → cmp (X a)) (η≡∗ a u) (x0 a) ≡ x1 u ) →
    ●/ind (∗ u) X x0 x1 h ≡ x1 u
  {-# REWRITE ●/ind/β₂ #-}


  ●/ind⁺ : (a : val (● A)) (B : val (● A) → tp pos)
    (x0 : (a : val A) → val (B (η a))) →
    (x1 : (u : ext) → val (B (∗ u))) →
    ((a : val A) → (u : ext) → subst (λ a → val (B a)) (η≡∗ a u) (x0 a) ≡ x1 u) →
    val (B a)

  ●/ind⁺/β₁ : (a : val A) (B : val (● A) → tp pos)
    (x0 : (a : val A) → val (B (η a))) →
    (x1 : (u : ext) → val (B (∗ u))) →
    (h : (a : val A) → (u : ext) → subst (λ a → val (B a)) (η≡∗ a u) (x0 a) ≡ x1 u) →
    ●/ind⁺ (η a) B x0 x1 h ≡ x0 a
  {-# REWRITE ●/ind⁺/β₁ #-}
  ●/ind⁺/β₂ : (u : ext) (B : val (● A) → tp pos)
    (x0 : (a : val A) → val (B (η a))) →
    (x1 : (u : ext) → val (B (∗ u))) →
    (h : (a : val A) → (u : ext) → subst (λ a → val (B a)) (η≡∗ a u) (x0 a) ≡ x1 u) →
    ●/ind⁺ (∗ u) B x0 x1 h ≡ x1 u
  {-# REWRITE ●/ind⁺/β₂ #-}
