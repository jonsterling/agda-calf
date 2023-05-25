{-# OPTIONS --cubical-compatible --prop --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.Eq where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Relation.Binary.PropositionalEquality

postulate
  eq : (A : tp pos) → val A → val A → tp pos
  eq/intro : ∀ {A v1 v2} → v1 ≡ v2 → val (eq A v1 v2)
  eq/ref : ∀ {A v1 v2} → cmp (F (eq A v1 v2)) → v1 ≡ v2

  eq/uni : ∀ {A v1 v2} → (p q : cmp (F (eq A v1 v2))) →
    (u : ext) → p ≡ q
