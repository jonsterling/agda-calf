{-# OPTIONS --rewriting #-}

module Examples.Gcd.Clocked where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid

open import Calf costMonoid
open import Calf.Data.Nat
open import Data.Nat using (_≤_; z≤n)
open import Calf.Data.Product using (unit)
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BoundedFunction costMonoid

open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality as P

open import Examples.Gcd.Euclid

{- Alternative definition of gcd with an explicit clock parameter.
   It is easier to see the computational behavior of the code in this version:
   1) when the clock is nonzero: the algorithm proceeds as normal
   2) clock is zero: algorithm terminates
   Crucially, if the recursor is by-name, then the value of the clock does not
   affect asymptotic behavior of the algorithm.
   Two things one can do in calf:
   1) give a good characterization of the clock in terms of the input by refining the raw recurrence (see Refine.agda)
   2) give a good characterization for of the clock for running the code; this usually
   means finding a clock computation that is simpler to compute
   than the "good" upperbound. For gcd, one can reuse the argument as the clock (see Spec.agda)
-}
gcd/clocked : cmp (Π nat λ _ → Π gcd/i λ _ → F nat)
gcd/clocked zero (x , y , h) = ret x
gcd/clocked (suc k) (x , 0 , h) =  ret {nat} x
gcd/clocked (suc k) (x , suc y , h) =
  bind {mod-tp x (suc y) triv} (F nat) (mod x (suc y) triv)
  λ { (z , eqn2) →
  let h2 = P.subst (λ k → suc k ≤ suc y) (P.sym eqn2) (m%n<n x _) in
  gcd/clocked k (suc y , z , h2) }

gcd : cmp (Π gcd/i λ _ → F nat)
gcd i = gcd/clocked (gcd/depth i) i

-- cost of clocked gcd is bounded by for any (not necessarily safe)
-- instantiation of the clock
gcd/clocked≤gcd/depth : ∀ k i → IsBounded nat (gcd/clocked k i) (gcd/depth i)
gcd/clocked≤gcd/depth zero i = bound/relax (λ _ → z≤n) bound/ret
gcd/clocked≤gcd/depth (suc k) (x , zero , h) = bound/ret
gcd/clocked≤gcd/depth (suc k) (x , y@(suc _) , h) rewrite gcd/depth-unfold-suc {h = h} =
  bound/step 1 _ (gcd/clocked≤gcd/depth k (y , x % y , m%n<n x _))

gcd≤gcd/depth : ∀ i → IsBounded nat (gcd i) (gcd/depth i)
gcd≤gcd/depth i = gcd/clocked≤gcd/depth (gcd/depth i) i

gcd/bounded : cmp (Ψ gcd/i (λ { _ → nat }) gcd/depth)
gcd/bounded = gcd , gcd≤gcd/depth
