{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Upper (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction costMonoid
open import Calf.Eq

-- postulate
--   le/ext : ◯ (cmp (F nat)) → ◯ (cmp (F nat)) → tp neg
--   le/ext/decode : ∀ {p q} → cmp (le/ext p q) ≡ ((u : ext) → p u ≤ q u)

data ub (A : tp pos) : cmp (F A) → cmp cost → □ where
  ub/intro : ∀ {e p q} (a : val A) →
    q ≤ p →
    cmp (F (eq (U(F A)) e (step' (F A) q (ret {A} a)))) →
    ub A e p

-- Alternative definition. Either way cannot have
-- induction for ub and rewrite rule for ub⁻
-- postulate
--   ub : (A : tp pos) → cmp (F A) → ℕ → □
--   ub/out : ∀ {A e p} → ub A e p →
--     Σ ℕ λ q →
--     Σ (val A) λ a →
--     Σ q ≤ p λ h →
--     cmp (eq (U(F A)) e (step' (F A) q (ret a)))
--   {-# REWRITE ub/decode #-}

postulate
  ub⁻ : (A : tp pos) → cmp (F A) → cmp cost → tp neg
  ub⁻/decode : ∀ {A e p} → iso (ub A e p) (cmp (ub⁻ A e p))

ub/relax : ∀ {A e p p'} → p ≤ p' → ub A e p → ub A e p'
ub/relax h (ub/intro {q = q} a h1 eqn) = ub/intro {q = q} a (≤-trans h1 h) eqn
