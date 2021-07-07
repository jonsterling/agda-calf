{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Upper (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Eq
open import Calf.Step costMonoid

record IsBounded (A : tp pos) (e : cmp (F A)) (c : cmp cost) : □ where
  constructor ⇓_withCost_[_,_]
  field
    result : val A
    c' : ℂ
    h-bounded : ◯ (c' ≤ c)
    h-≡ : cmp (F (eq (U (F A)) e (step (F A) c' (ret result))))

IsBounded⁻ : (A : tp pos) → cmp (F A) → cmp cost → tp neg
IsBounded⁻ A e p = meta (IsBounded A e p)

bound/relax : ∀ {A e p p'} → ◯ (p ≤ p') → IsBounded A e p → IsBounded A e p'
bound/relax h (⇓ result withCost c' [ h-bounded , h-≡ ]) = ⇓ result withCost c' [ (λ u → ≤-trans (h-bounded u) (h u)) , h-≡ ]
