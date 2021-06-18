{-# OPTIONS --prop --rewriting #-}

module Examples.Gcd-new where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Upper
open import Calf.Eq
open import Data.Nat as Nat
open import Calf.Connectives
open import Function
open import Relation.Binary.PropositionalEquality as P
open import Calf.Types.Nat
open import Examples.Gcd
open import Induction.WellFounded
open import Induction
open import Data.Nat.Properties
open import Calf.Refinement
open import Data.Nat.DivMod
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Unit using (tt)
open import Function.Base using (_on_)
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
gcd/clocked : cmp (Π (U (meta ℕ)) λ _ → Π gcd/i λ _ → F nat)
gcd/clocked zero (x , y , h) = ret x
gcd/clocked (suc k) (x , y , h) = rec y (const (F nat)) (ret {nat} x)
  (λ y' _ →
    bind {mod-tp x (succ y') tt} (F nat) (mod x (succ y') tt)
    λ { (z , eqn2) →
    let h2 = P.subst (λ k → suc k ≤ toℕ (succ y')) (P.sym eqn2) (m%n<n' (toℕ x) _ tt) in
    gcd/clocked k (succ y' , z , h2) })

gcd/code : cmp (Π gcd/i λ _ → F nat)
gcd/code i = gcd/clocked (gcd/cost (to-ext i)) i

gcd/i/eq : ∀ {x x' y y' h h'} →
        (eqn : x ≡ x') →
        (eqn2 : y ≡ y') →
        _≡_ {A = m>n} (x , y , h) (x' , y' , h')
gcd/i/eq {x} {x'} {y} {y'} {h} {h'} eqn eqn2 = Inverse.f Σ-≡,≡↔≡ (eqn , Inverse.f Σ-≡,≡↔≡ (P.trans (fst/subst eqn) eqn2 ,
  <-irrelevant _ _))

-- cost of clocked gcd is bounded by for any instantiation of the clock
gcd/clocked≤gcd/cost : ∀ k i → ub nat (gcd/clocked k i) (gcd/cost (to-ext i))
gcd/clocked≤gcd/cost 0 i = ub/ret (gcd/cost (to-ext i))
gcd/clocked≤gcd/cost (suc k) i@(x , y , z) rewrite gcd/cost-unfold' i =
  ub/rec
  (const nat)
  y
  (ret {nat} x)
  (λ y' →
    bind {mod-tp x (succ y') tt} (F nat) (mod x (succ y') tt)
    λ { (z , eqn2)
          → let h2
                  = P.subst (λ k → suc k ≤ toℕ (succ y')) (P.sym eqn2)
                    (m%n<n' (toℕ x) _ tt)
            in gcd/clocked k (succ y' , z , h2)
      })
  0
  (λ n' → suc (gcd/cost (suc n' , toℕ x % suc n' , m%n<n (toℕ x) n')))
  (ub/ret 0)
  λ y' → ub/bind/suc {e = mod x (succ y') tt} {f = λ { (z , eqn2)
          → let h2
                  = P.subst (λ k → suc k ≤ toℕ (succ y')) (P.sym eqn2)
                    (m%n<n' (toℕ x) _ tt)
            in gcd/clocked k (succ y' , z , h2)
      }} (gcd/cost (suc (toℕ y') , toℕ x % suc (toℕ y') , m%n<n (toℕ x) (toℕ y')))
  (ub/step/suc 0 (ub/ret 0))
  λ {(z , eqn2) →
  let h2 = P.subst (λ k → suc k ≤ toℕ (succ y')) (P.sym eqn2) (m%n<n' (toℕ x) (toℕ (succ y')) tt) in
  let g = gcd/clocked≤gcd/cost k (succ y' , z , h2) in
  let h3 = to-ext-unfold (succ y' , z , h2) in
  let h4 = P.subst (λ cost → ub nat (gcd/clocked k (succ y' , z , h2)) (gcd/cost cost)) h3 g in
  let h5 = gcd/i/eq {h = h2} {h' = m%n<n (toℕ x) (toℕ y')} refl eqn2 in
  let h6 = P.subst (λ cost → ub nat (gcd/clocked k (succ y' , z , h2)) (gcd/cost cost)) h5 h4 in
  h6 }

gcd : cmp (Ψ gcd/i (λ { _ → nat }) e/gcd gcd/cost)
gcd = gcd/code ,
      λ { (x , y , h) →
          iso.fwd ub⁻/decode
          (gcd/clocked≤gcd/cost (gcd/cost (to-ext (x , y , h))) ((x , y , h)))
      }

