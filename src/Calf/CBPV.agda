{-# OPTIONS --rewriting #-}

-- The basic CBPV metalanguage.

module Calf.CBPV where

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

variable
  A B C : tp pos
  X Y Z : tp neg


-- Value types

postulate
  meta⁺ : Set → tp pos
  meta⁺/decode : {𝕊 : Set} → val (meta⁺ 𝕊) ≡ 𝕊
  {-# REWRITE meta⁺/decode #-}

Σ⁺ : (A : tp pos) (B : val A → tp pos) → tp pos
Σ⁺ A B = meta⁺ (Σ (val A) λ a → val (B a))


-- Computation types

postulate
  ret : val A → cmp (F A)
  bind : (X : tp neg) → cmp (F A) → (val A → cmp X) → cmp X

  bind/β : {a : val A} {f : val A → cmp X} → bind X (ret {A} a) f ≡ f a
  bind/η : {e : cmp (F A)} → bind (F A) e ret ≡ e
  bind/assoc : {e : cmp (F A)} {f : val A → cmp (F B)} {g : val B → cmp X} →
    bind X (bind (F B) e f) g ≡ bind X e (λ a → bind X (f a) g)
  {-# REWRITE bind/β bind/η bind/assoc #-}

  Π : (A : tp pos) (P : val A → tp neg) → tp neg
  Π/decode : {X : val A → tp neg} → val (U (Π A X)) ≡ ((a : val A) → cmp (X a))
  {-# REWRITE Π/decode #-}

  Σ⁻ : (A : tp pos) (X : val A → tp neg) → tp neg
  Σ⁻/decode : {X : val A → tp neg} → val (U (Σ⁻ A X)) ≡ Σ (val A) λ a → cmp (X a)
  {-# REWRITE Σ⁻/decode #-}

_⋉_ : tp pos → tp neg → tp neg
A ⋉ X = Σ⁻ A (λ _ → X)
