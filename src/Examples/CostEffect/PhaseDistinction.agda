{-# OPTIONS --prop --without-K --rewriting #-}

-- This file adds the phase distinction for extension.

open import Calf.CostMonoid

module Examples.CostEffect.PhaseDistinction (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Examples.CostEffect.CostEffect costMonoid
open import Calf.PhaseDistinction costMonoid

open import Relation.Binary.PropositionalEquality as P

-- Underneath the open modality, we ensure that the abstract types
-- that force you to take steps don't do anything.

postulate
  ►/ext : ∀ c A → ◯ (val (► c A) → val A)
  ►/ext/β : ∀ {A} {z : ext} {u : val A} {c} → ►/ext c A z (►/ret c A u) ≡ u
  {-# REWRITE ►/ext/β #-}

  ►/ext/η : ∀ {A} {c} (z : ext) (u : val (► c A)) → ►/ret c A (►/ext c A z u) ≡ u

►/ext/match : ∀ {A X c} {u : val (► c A)} {f : val A → cmp X} {z : ext} → ►/match X u f ≡ f (►/ext c A z u)
►/ext/match {A} {X} {c} {u} {f} {z} rewrite (P.sym (►/ext/η z u)) = step'/ext X (f (►/ext c A z u)) c z

postulate
  ▷/ext : ∀ c X → ◯ (cmp (▷ c X) → cmp X)
  ▷/ext/β : ∀ {X} {z : ext} {u : cmp X} {c} → ▷/ext c X z (▷/ret c X u) ≡ u
  {-# REWRITE ▷/ext/β #-}

  ▷/ext/η : ∀ {X} {c} (z : ext) (u : cmp (▷ c X)) → ▷/ret c X (▷/ext c X z u) ≡ u

▷/ext/match : ∀ {Y X c} {u : cmp (▷ c Y)} {f : cmp Y → cmp X} {z : ext} → ▷/match X u f ≡ f (▷/ext c Y z u)
▷/ext/match {Y} {X} {c} {u} {f} {z} rewrite (P.sym (▷/ext/η z u)) = step'/ext X (f (▷/ext c Y z u)) c z

►/ind : ∀ {A c} {P : val (► c A) → □} → ◯ ((∀ x → P (►/ret c _ x)) → ∀ x → P x)
►/ind {A} {c} z f x rewrite (P.sym (►/ext/η z x)) = f (►/ext c A z x)
