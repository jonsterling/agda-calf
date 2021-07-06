{-# OPTIONS --prop --rewriting #-}

module Examples.Gcd.Clocked where

open import Calf.CostMonoid
import Calf.CostMonoids as CM

open import Calf CM.ℕ-CostMonoid
open import Calf.Types.Nat

open import Data.Nat as Nat
open import Function
open import Relation.Binary.PropositionalEquality as P
open import Examples.Gcd.Euclid
open import Induction.WellFounded
open import Induction
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Unit using (tt)
open import Function.Base using (_on_)
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.HeterogeneousEquality as H
open import Agda.Builtin.Nat using (div-helper; mod-helper)
import Level as L
open import Relation.Binary using (Rel)
open import Relation.Unary using (Pred; _⊆′_)
open import Data.Nat.DivMod.Core
open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

{- Alternative definition of gcd with an explicit clock parameter.
   It is easier to see the computational behavior of the code in this version:
   1) when the clock is nonzero: the algorithm proceeds as normal
   2) clock is zero: algorithm terminates
   Crucially, if the recursor is by-name, then the value of the clock does not
   affect asymptotic behavior of the algorithm.
   Two things one can do in sqtt:
   1) give a good characterization of the clock in terms of the input by refining the raw recurrence (see Gcd-Rec.agda)
   2) give a good characterization for of the clock for running the code; this usually
   means finding a clock computation that is simpler to compute
   than the "good" upperbound. For gcd, one can reuse the argument as the clock (see Gcd-Ext.agda)
-}
gcd/clocked : cmp (Π nat λ _ → Π gcd/i λ _ → F nat)
gcd/clocked zero (x , y , h) = ret x
gcd/clocked (suc k) (x , 0 , h) =  ret {nat} x
gcd/clocked (suc k) (x , suc y , h) =
  bind {mod-tp x (suc y) tt} (F nat) (mod x (suc y) tt)
  λ { (z , eqn2) →
  let h2 = P.subst (λ k → suc k ≤ suc y) (P.sym eqn2) (m%n<n' x _ tt) in
  gcd/clocked k (suc y , z , h2) }

gcd : cmp (Π gcd/i λ _ → F nat)
gcd i = gcd/clocked (gcd/cost i) i

ub/step/suc : ∀ {A e} (p : ℕ) →
  ub A e p →
  ub A (step (F A) 1 e) (suc p)
ub/step/suc {A} {e} p (ub/intro {q = q1} a h1 h2) =
  ub/intro {q = suc q1} a (λ u → s≤s (h1 u)) (ret (eq/intro
    (
      begin
      step (F A) 1 e ≡⟨ P.cong (step (F A) 1) (eq/ref h2) ⟩
      step (F A) 1 (step (F A) q1 (ret a))
      ∎
    )
  ))
  where open ≡-Reasoning

-- cost of clocked gcd is bounded by for any (not necessarily safe)
-- instantiation of the clock
gcd/clocked≤gcd/cost : ∀ k i → ub nat (gcd/clocked k i) (gcd/cost i)
gcd/clocked≤gcd/cost Nat.zero i = ub/relax (λ _ → z≤n) ub/ret
gcd/clocked≤gcd/cost (suc k) (x , Nat.zero , h) = ub/ret
gcd/clocked≤gcd/cost (suc k) (x , suc y , h) rewrite gcd/cost-unfold-suc {x} {y} {h} =
  ub/step/suc
  {e = gcd/clocked k (suc y , x % suc y , m%n<n' x _ tt)}
  (gcd/cost (suc y , x % suc y , m%n<n' x _ tt))
  (gcd/clocked≤gcd/cost k (suc y , x % suc y , m%n<n' x _ tt))

gcd≤gcd/cost : ∀ i → ub nat (gcd i) (gcd/cost i)
gcd≤gcd/cost i = gcd/clocked≤gcd/cost (gcd/cost i) i

gcd/bounded : cmp (Ψ gcd/i (λ { _ → nat }) gcd/cost)
gcd/bounded = gcd , gcd≤gcd/cost
