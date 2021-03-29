
{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import Cost
open import Num
open import PhaseDistinction
open import Connectives
open import Refinement
open import Upper
open import Eq

open import Gcd
open import Data.Nat.GCD
open import Data.Nat.DivMod
open import Data.Nat
open import Data.Product
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality as P
open import Induction.WellFounded
open import Relation.Binary.Construct.On as On
open import Function.Base using (_on_)
open import Function
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Product.Properties

gcd' : m>n → ℕ
gcd' (m , (n , h)) = gcd′ m n (<-wellFounded m) h

gcd′-ext : ∀ {m n h} →
    {acc1 acc2 : Acc _<_ m} →
    gcd′ m n acc1 h ≡ gcd′ m n acc2 h
gcd′-ext {m} {zero} {h} {acc1} {acc2} = refl
gcd′-ext {m} {suc n'} {h} {acc rec1} {acc rec2} =
  gcd′-ext {suc n'} {m % suc n'} {acc1 = rec1 (suc n') h} {acc2 = rec2 (suc n') h}

gcd′-ext' : ∀ {m n h n' h'} →
    {acc1 acc2 : Acc _<_ m} →
    (_≡_ {A = m>n} (m , n , h) (m , n' , h')) →
    gcd′ m n acc1 h ≡ gcd′ m n' acc2 h'
gcd′-ext' {m} {n} {h} {n'} {h'} {acc1 = acc1} {acc2 = acc2} refl =
  gcd′-ext {m} {n} {h} {acc1 = acc1} {acc2 = acc2}

gcd'-unfold : ∀ {x y h} → gcd' (x , y , h) ≡
                        if {const ℕ} y x (λ y' → gcd' (suc y' , x % suc y' , m%n<n x y'))
gcd'-unfold {x} {zero} {h} = refl
gcd'-unfold {x} {y@(suc y')} {h} = gcd′-ext {m = suc y'} {n = x % suc y'}

gcd/code≡gcd' : ∀ x y h → ◯ (gcd/code (x , y , h) ≡
                              ret {num} (to-num (gcd' (to-nat x , to-nat y , h))))
gcd/code≡gcd' x y h = All.wfRec (wellFounded to-nat <-wellFounded) _ P ih y x h

  where
  P = (λ y → ∀ x h → ◯ (gcd/code (x , y , h) ≡
                        ret {num} (to-num (gcd' (to-nat x , to-nat y , h)))))

  i/suc : ∀ {y' y x h} →
      (u : ext) →
      (eqn : suc (to-nat y') ≡ to-nat y) →
      WfRec (_<_ on to-nat) P y →
    gcd/body (x , to-num (suc (to-nat y')) , h) (λ i _ → gcd/code i) ≡
    ret {num} (to-num (gcd' (to-nat x , suc (to-nat y') , h)))
  i/suc {y'} {y} {x} {h} u y'+1≡y step with mod/cost {x} {to-num (suc (to-nat y'))} {tt}
  ... | (ub/intro {q = q} (z , eqn2) bound eqn) with  mod x (to-num (suc (to-nat y'))) tt  | eq/ref eqn
  ... | _ | refl with step' (F num) q
                      (gcd/code (to-num (suc (to-nat y')) , z ,
                      P.subst (λ k → suc k ≤ suc (to-nat y')) (symm eqn2) (m%n<n' (to-nat x) _ tt))) |  step'/ext (F num)
                      (gcd/code (to-num (suc (to-nat y')) , z ,
                      P.subst (λ k → suc k ≤ suc (to-nat y')) (symm eqn2) (m%n<n' (to-nat x) _ tt))) q u
  ... | _ | refl =
    let h2 = P.subst (λ k → suc k ≤ suc (to-nat y')) (symm eqn2) (m%n<n' (to-nat x) _ tt) in
    let h3 = P.subst (λ yy → yy > to-nat z) (y'+1≡y) h2 in
    let g = step z h3 (to-num (suc (to-nat y'))) h2 u in
    let h4 : _≡_ {A = m>n} (suc (to-nat y') , to-nat z , h2) (suc (to-nat y') , to-nat x % suc (to-nat y') , m%n<n' (to-nat x) _ tt)
        h4 = Inverse.f Σ-≡,≡↔≡ (refl ,
              Inverse.f Σ-≡,≡↔≡ (eqn2 , ≤-irrelevant _ _)) in
    P.trans g (P.cong (ret {num} ∘ to-num)
      (gcd′-ext' h4 ))

  ih : ∀ y → WfRec (_<_ on to-nat) P y → P y
  ih y step = ifz (λ n → meta (to-nat y ≡ n → P (to-num n))) y
    (λ eqn x h u → refl)
    (λ y' h' eqn x h u →
        P.subst (λ code → code ≡ ret {num} (to-num (gcd' (to-nat x , suc (to-nat y') , h))) )
        (P.sym (FixPoint.unfold-wfRec (lt/cost/wf {gcd/i} {e/gcd} {gcd/cost})
             (const (cmp (F num)))
             gcd/body
             gcd/body-ext {(x , to-num (suc (to-nat y')) , h)}))
        (i/suc {y'} {y} {x} {h} u h' step) )
        refl

