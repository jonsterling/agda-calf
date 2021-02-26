{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Eq

ub/ret : ∀ {A a} (n : val nat) → ub A (ret a) (λ _ → ret zero)
ub/ret n = ub/intro {q = λ _ → ret zero} (λ u → ret le/zero) eq/intro

-- Need to understand with-abstraction.
ub/step : ∀ {A e} (p q : cmp 𝒞) → 
  ub A e p → 
  ub A (step' (F A) q e) (p ⊕ q)
ub/step p q (ub/intro {q = q1} {a = a} h1 h2) with eq/ref h2 | p ⊕ q | add/comm/ext {p = p} {q = q}
...                                              | refl | _ | refl = ub/intro {q = q ⊕ q1}
   (le/add/ext {q} {q1} {q} {p} (le/refl/ext {q}) h1) eq/intro