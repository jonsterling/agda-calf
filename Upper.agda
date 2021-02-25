{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Eq

postulate
  ub : ∀ {B} → cmp B → cmp 𝒞 → □ 
  ub/intro : ∀ {A e p q a} → 
    cmp (le/ext p q) → 
    val (eq (U(F A)) e (step' (F A) q (ret a))) → 
    ub {F A} e p
