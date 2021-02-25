{-# OPTIONS --prop --rewriting #-}

-- This file adds the phase distinction for extension.

module PhaseDistinction where

open import Prelude
open import Metalanguage
open import CostEffect

postulate
  ext : Ω
  step/ext : ∀ X → (e : cmp X) → ext → step X e ≡ e
  -- sadly the above cannot be made an Agda rewrite rule

postulate
  ►/ext : ∀ A → ext → val (► A) → val A
  ►/ext/β : ∀ {A} {z : ext} {u : val A} → ►/ext A z (►/ret A u) ≡ u
  {-# REWRITE ►/ext/β #-}

  ►/ext/η : ∀ {A} (z : ext) (u : val (► A)) → ►/ret A (►/ext A z u) ≡ u

►/ext/match : ∀ {A X} {u : val (► A)} {f : val A → cmp X} {z : ext} → ►/match X u f ≡ f (►/ext A z u)
►/ext/match {A} {X} {u} {f} {z} rewrite (symm (►/ext/η z u)) = step/ext X (f (►/ext A z u)) z

postulate
  ▷/ext : ∀ X → ext → cmp (▷ X) → cmp X
  ▷/ext/β : ∀ {X} {z : ext} {u : cmp X} → ▷/ext X z (▷/ret X u) ≡ u
  {-# REWRITE ▷/ext/β #-}

  ▷/ext/η : ∀ {X} (z : ext) (u : cmp (▷ X)) → ▷/ret X (▷/ext X z u) ≡ u

▷/ext/match : ∀ {Y X} {u : cmp (▷ Y)} {f : cmp Y → cmp X} {z : ext} → ▷/match X u f ≡ f (▷/ext Y z u)
▷/ext/match {Y} {X} {u} {f} {z} rewrite (symm (▷/ext/η z u)) = step/ext X (f (▷/ext Y z u)) z
