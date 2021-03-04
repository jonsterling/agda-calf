{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Eq
open import Nat

ub/ret : ∀ {A a} (n : val nat) → ub A (ret a) cost/zero
ub/ret n = ub/intro {q = cost/zero} (le/zero/cost {cost/zero}) (ret (eq/intro refl))

-- Need to understand with-abstraction.
ub/step : ∀ {A e} (p q : cmp 𝒞) → 
  ub A e p → 
  ub A (step' (F A) q e) (p ⊕ q)
ub/step p q (ub/intro {q = q1} {a = a} h1 h2) with eq/ref h2 | p ⊕ q | eq/ref (add/comm/cost {p = p} {q = q})
...                                              | refl | _ | refl = ub/intro {q = q ⊕ q1}
   (le/add/cost {q} {q1} {q} {p} (le/refl/cost {q}) h1) (ret (eq/intro refl))