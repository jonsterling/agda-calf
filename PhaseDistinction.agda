{-# OPTIONS --prop --rewriting #-}

-- This file adds the phase distinction for extension.

module PhaseDistinction where

open import Prelude
open import Metalanguage
open import CostEffect

postulate
  ext : Ω

○ : □ → □
○ A = {{ ext }} → A

postulate
  step/ext : ∀ X → (e : cmp X) → ○ (step X e ≡ e)
  {-# REWRITE step/ext #-}


-- Underneath the open modality, we ensure that the abstract types
-- that force you to take steps don't do anything.

postulate
  ►/ext : ∀ A → ○ (► A ≡ A)
  {-# REWRITE ►/ext #-}

  ►/ret/ext : ∀ A a → ○ (►/ret A a ≡ a)
  {-# REWRITE ►/ret/ext #-}

  ▷/ext : ∀ X → ○ (▷ X ≡ X)
  {-# REWRITE ▷/ext #-}

  ▷/ret/ext : ∀ X x → ○ (▷/ret X x ≡ x)
  {-# REWRITE ▷/ret/ext #-}

{-
postulate
  ►/ext : ∀ A → ◯ (val (► A) → val A)
  ►/ext/β : ∀ {A} {z : ext} {u : val A} → ►/ext A z (►/ret A u) ≡ u
  {-# REWRITE ►/ext/β #-}

  ►/ext/η : ∀ {A} (z : ext) (u : val (► A)) → ►/ret A (►/ext A z u) ≡ u

►/ext/match : ∀ {A X} {u : val (► A)} {f : val A → cmp X} {z : ext} → ►/match X u f ≡ f (►/ext A z u)
►/ext/match {A} {X} {u} {f} {z} rewrite (symm (►/ext/η z u)) = let instance _ = z in refl

postulate
  ▷/ext : ∀ X → ◯ (cmp (▷ X) → cmp X)
  ▷/ext/β : ∀ {X} {z : ext} {u : cmp X} → ▷/ext X z (▷/ret X u) ≡ u
  {-# REWRITE ▷/ext/β #-}

  ▷/ext/η : ∀ {X} (z : ext) (u : cmp (▷ X)) → ▷/ret X (▷/ext X z u) ≡ u

▷/ext/match : ∀ {Y X} {u : cmp (▷ Y)} {f : cmp Y → cmp X} {z : ext} → ▷/match X u f ≡ f (▷/ext Y z u)
▷/ext/match {Y} {X} {u} {f} {z} rewrite (symm (▷/ext/η z u)) = let instance _ = z in refl


-}

►/ind : ∀ {A} {P : val (► A) → □} → ○ ((∀ x → P (►/ret A x)) → ∀ x → P x)
►/ind {A} {{z}} f = f


postulate
  ►/match/ext : ∀ {A X} {u : val A} {f : val A → cmp X} → ○ (►/match {A} X u f ≡ step X (f u))
  {-# REWRITE ►/match/ext #-}

  ▷/match/ext : ∀ {X Y} {e : cmp X} {f : cmp X → cmp Y} → ○ (▷/match {X} Y e f ≡ step Y (f e))
  {-# REWRITE ▷/match/ext #-}
