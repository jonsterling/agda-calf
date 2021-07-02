{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Upper (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction costMonoid
open import Calf.Eq

data ub (A : tp pos) : cmp (F A) → cmp cost → □ where
  ub/intro : ∀ {e p q} (a : val A) →
    ◯ (q ≤ p) →
    cmp (F (eq (U(F A)) e (step' (F A) q (ret {A} a)))) →
    ub A e p

ub⁻ : (A : tp pos) → cmp (F A) → cmp cost → tp neg
ub⁻ A e p = meta (ub A e p)

ub/relax : ∀ {A e p p'} → ◯ (p ≤ p') → ub A e p → ub A e p'
ub/relax h (ub/intro {q = q} a h1 eqn) = ub/intro {q = q} a (λ u → ≤-trans (h1 u) (h u)) eqn
