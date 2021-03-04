{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Eq

data ub (A : tp pos) : cmp (F A) → cmp 𝒞 → □ where
  ub/intro : ∀ {e p q a} → 
    cmp (le/cost q p) → 
    cmp (F (eq (U(F A)) e (step' (F A) q (ret a)))) → 
    ub A e p

-- Alternative definition. Either way cannot have 
-- induction for ub and rewrite rule for ub⁻
-- postulate 
--   ub : (A : tp pos) → cmp (F A) → cmp 𝒞 → □ 
--   ub/decode : ∀ {A e p} → ub A e p ≡ 
--     Σ (cmp 𝒞) λ q → 
--     Σ (val A) λ a → 
--     Σ (cmp (le/ext q p)) λ _ → 
--     val (eq (U(F A)) e (step' (F A) q (ret a)))
--   {-# REWRITE ub/decode #-}

postulate 
  ub⁻ : (A : tp pos) → cmp (F A) → cmp 𝒞 → tp neg 
  ub⁻/decode : ∀ {A e p} → ub A e p ≡ cmp (ub⁻ A e p)