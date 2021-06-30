{-# OPTIONS --prop --without-K --rewriting #-}

-- This file adds the phase distinction for extension.

open import Calf.CostMonoid

module Calf.PhaseDistinction (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as P

postulate
  ext : Ω

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

postulate
  step'/ext : ∀ X → (e : cmp X) → (c : ℂ) → ◯ (step' X c e ≡ e)
  -- sadly the above cannot be made an Agda rewrite rule