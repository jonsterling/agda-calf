{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Eq where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction

postulate
  eq : (A : tp pos) → val A → val A → tp pos
  eq/intro : ∀ {A v1 v2} → v1 ≡ v2 → val (eq A v1 v2)
  eq/ref : ∀ {A v1 v2} → cmp (F(eq A v1 v2)) → v1 ≡ v2