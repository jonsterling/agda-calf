{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Upper
open import Eq
open import Data.Nat as Nat
open import Connectives
open import Function
open import Relation.Binary.PropositionalEquality as P
open import Num
open import Gcd
open import Induction.WellFounded
open import Induction
open import Data.Nat.Properties
open import Refinement
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
gcd/clocked : cmp (Π (U (meta ℕ)) λ _ → Π gcd/i λ _ → F num)
gcd/clocked zero (x , y , h) = ret x
gcd/clocked (suc n) (x , y , h) = ifz (const (F num)) y (ret {num} x)
  (λ y' eqn →
    bind {mod-tp x y (suc≢0 eqn)} (F num) (mod x y (suc≢0 eqn))
    λ { (z , eqn2) →
    let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
    gcd/clocked n (y , z , h2) })

gcd/code : cmp (Π gcd/i λ _ → F num)
gcd/code i = gcd/clocked (gcd/cost (to-ext i)) i

gcd/next/eq : ∀ {x y y' z} →
        (eqn : suc (to-nat y') ≡ to-nat y) →
        (eqn2 : to-nat z ≡ _%_ (to-nat x) (to-nat y) {suc≢0 eqn}) →
        let h1 = suc≢0 eqn in
        _≡_ {A = m>n}
          (to-nat y , to-nat z , P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' (to-nat x) (to-nat y) (suc≢0 eqn)))
          (suc (to-nat y') , to-nat x % (suc (to-nat y')), m%n<n (to-nat x) (to-nat y'))
gcd/next/eq {x} {y} {y'} {z} eqn eqn2 =
    let eqn3 = P.subst (λ yy → (h : suc (to-nat y') ≡ yy) → to-nat z ≡ _%_ (to-nat x) yy {P.subst (λ n → False (n ≟ 0)) h tt}) (symm eqn)
              (λ h → P.subst (λ eqn → to-nat z ≡ _%_ (to-nat x) (to-nat y) {P.subst (λ n → False (n ≟ 0)) eqn tt}) (uip eqn h) eqn2)
              refl in
    Inverse.f Σ-≡,≡↔≡ (
      symm eqn , Inverse.f Σ-≡,≡↔≡ (
        P.trans (fst/subst (symm eqn))
          (P.trans eqn3 refl) ,
          ≤-irrelevant _ _))

-- cost of clocked gcd is bounded by for any instantiation of the clock
gcd/clocked≤gcd/cost : ∀ k i → ub num (gcd/clocked k i) (gcd/cost (to-ext i))
gcd/clocked≤gcd/cost 0 i = ub/ret (gcd/cost (to-ext i))
gcd/clocked≤gcd/cost (suc k) i@(x , y , z) rewrite gcd/cost-unfold' i =
  ub/ifz (const num) y (ret {num} x) (λ y' eqn → bind {mod-tp x y (suc≢0 eqn)} (F num) (mod x y (suc≢0 eqn))
  λ { (z , eqn2) →
  let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
  gcd/clocked k (y , z , h2) })
  0 ((λ n' → suc (gcd/cost (suc n' , to-nat x % suc n' , m%n<n (to-nat x) n'))))
  (ub/ret 0)
  λ y' eqn →
  ub/bind/suc {e = mod x y (suc≢0 eqn)}
  {f = λ { (z , eqn2)
    → let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn))
      in gcd/clocked k (y , z , h2)
  }}
  (e/mod-tp x y (suc≢0 eqn))
  (gcd/cost (suc (to-nat y') , to-nat x % suc (to-nat y') , m%n<n (to-nat x) (to-nat y')))
  mod/cost
  (λ {(z , eqn2) →
  let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
  let h4 = P.cong gcd/cost (gcd/next/eq {x} {y} {y'} {z} eqn eqn2) in
  let h5 = symm (to-ext-unfold (y , z , h2)) in
  let g = gcd/clocked≤gcd/cost k (y , z , h2) in
  P.subst (λ cost → ub num (gcd/clocked k (y , z , h2)) cost)
  (P.trans (P.cong gcd/cost (symm h5)) h4) g })

gcd : cmp (Ψ gcd/i (λ { _ → num }) e/gcd gcd/cost)
gcd = gcd/code ,
      λ { (x , y , h) →
          iso.fwd ub⁻/decode
          (gcd/clocked≤gcd/cost (gcd/cost (to-ext (x , y , h))) ((x , y , h)))
      }

