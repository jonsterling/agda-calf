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
  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X

  bind/beta : ∀ {A X} {v : val A} {f : (x : val A) → cmp X} → bind X (ret v) f ≡ f v
  bind/eta : ∀ {A} {e : cmp (F A)} → bind (F A) e ret ≡ e
  {-# REWRITE bind/beta bind/eta #-}

  bind/assoc : ∀ {A B C} {e : cmp (F A)} {f1 : val A → cmp (F B)} {f2 : val B → cmp C} →
    bind C (bind (F B) e f1) f2 ≡ bind C e (λ v → bind C (f1 v) f2)
  {-# REWRITE bind/assoc #-}

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

  -- agda sets
  meta : Set → tp neg
  meta/out : ∀ {A} → val (U (meta A)) ≡ A
  {-# REWRITE meta/out #-}

  bind/meta : ∀ A 𝕊 𝕋 e f (g : 𝕊 → 𝕋) → g (bind {A} (meta 𝕊) e f) ≡ bind {A} (meta 𝕋) e (λ a → g(f a))
  bind/idem : ∀ A 𝕊 e (f : val A → val A → 𝕊) → bind {A} (meta 𝕊) e (λ a → (bind {A} (meta 𝕊) e (λ a' → f a a'))) ≡ bind {A} (meta 𝕊) e (λ a → f a a)

{-# POLARITY meta ++ #-}
