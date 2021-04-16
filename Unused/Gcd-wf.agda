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

gcd/body/prf : (i@(x , y , h) : val gcd/i) → (y' : val num) → (eqn : suc (to-nat y') ≡ to-nat y) →
              (z : val num) → (eqn2 : to-nat z ≡ _%_ (to-nat x) (to-nat y) {suc≢0 eqn}) →
              let h1 = suc≢0 eqn in
              lt/cost e/gcd gcd/cost
              (y , z , P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ h1))
              (x , y , h)
gcd/body/prf i1@(x , y , h) y' eqn z eqn2 =
    let h1 = suc≢0 eqn in
    let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ h1) in
    let i2 = (y , (z , h2)) in
    let C = λ x n → to-nat x > n in
    let p = (to-nat z ,
                P.subst (λ a → to-nat y > to-nat a) (symm (nat-num z))
                (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
                (m%n<n' (to-nat x) (to-nat y)
                (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt)))) in
    let h3 = snd/subst {B = ℕ} {C = λ x n → to-nat x > n}
              {p = p}  (symm (nat-num y)) in
    let h4 = ≡-subst-removable (_>_ (to-nat y))
              (symm (fst/subst {C = C} {p = p} (symm (nat-num y))))
              (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
              (m%n<n' (to-nat x) (to-nat y)
              (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt))) in
    let h5 = ≡-subst-removable (λ k → suc k ≤ to-nat y) (symm eqn2)
              (m%n<n' (to-nat x) (to-nat y)
              (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt)) in
    let h6 = ≡-subst-removable (λ n → to-nat y > n) (symm (fst/subst {C = C} {p = p} (symm (nat-num y))))
              (P.subst (λ x₁ → to-nat x₁ > to-nat z) (symm (nat-num y))
              (P.subst (λ a → to-nat y > to-nat a) (symm (nat-num z))
              (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
              (m%n<n' (to-nat x) (to-nat y)
              (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt))))) in
    let h7 = ≡-subst-removable (λ x₁ → to-nat x₁ > to-nat z) (symm (nat-num y))
              (P.subst (λ a → to-nat y > to-nat a) (symm (nat-num z))
              (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
              (m%n<n' (to-nat x) (to-nat y)
              (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt)))) in
    let h8 = ≡-subst-removable (λ a → to-nat y > to-nat a) (symm (nat-num z))
              (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
              (m%n<n' (to-nat x) (to-nat y)
              (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt))) in
    let h9 = H.trans (H.≡-to-≅ h3) (H.trans h6 (H.trans h7 h8)) in
    let h10 = H.trans h4 (H.sym h9)  in
    let h11 : P.subst (_>_ (to-nat y))
            (symm (fst/subst (symm (nat-num y))))
            (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
            (m%n<n' (to-nat x) (to-nat y)
              (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt)))
            ≡
            snd
            (P.subst (λ a → Σ ℕ (λ a₁ → to-nat a > a₁)) (symm (nat-num y))
            (to-nat z ,
              P.subst (λ a → to-nat y > to-nat a) (symm (nat-num z))
              (P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
              (m%n<n' (to-nat x) (to-nat y)
                (P.subst (λ n → cmp (meta (False (n ≟ 0)))) eqn tt)))))
        h11 = H.≅-to-≡ h10 in
    let p' = (to-nat y ,
                  P.subst (λ a → to-nat x > to-nat a) (symm (nat-num y)) h) in
    let h12 = snd/subst {C = C} {p = p'} (symm (nat-num x)) in
    let h13 = ≡-subst-removable (λ m → m < to-nat x) (symm (fst/subst {C = C} {p = p'} (symm (nat-num x))))
              (P.subst (λ x₁ → to-nat y < to-nat x₁) (symm (nat-num x))
              (P.subst (λ a → to-nat x > to-nat a) (symm (nat-num y)) h)) in
    let h14 = ≡-subst-removable (λ x₁ → to-nat y < to-nat x₁) (symm (nat-num x))
              (P.subst (λ a → to-nat x > to-nat a) (symm (nat-num y)) h) in
    let h15 = ≡-subst-removable (λ a → to-nat x > to-nat a) (symm (nat-num y)) h in
    let h16 = ≡-subst-removable (_>_ (to-nat x)) (symm (fst/subst (symm (nat-num x)))) h in
    let h17 = H.trans (≡-to-≅ h12) (H.trans h13 (H.trans h14 h15)) in
    let h18 = H.≅-to-≡ (H.trans h16 (H.sym h17)) in
    let h19 = ( P.subst₂ (_<_ on gcd/cost)
          { (to-nat y , (to-nat z , h2)) }
          { iso.fwd (Ext.rep e/gcd) i2 }
          { (to-nat x , (to-nat y , h)) }
          { iso.fwd (Ext.rep e/gcd) i1 }
          ( Inverse.f Σ-≡,≡↔≡ (refl ,
              Inverse.f Σ-≡,≡↔≡ (symm (fst/subst (symm (nat-num y))) , h11 )))
          (Inverse.f Σ-≡,≡↔≡ (refl , Inverse.f Σ-≡,≡↔≡ (symm (fst/subst (symm (nat-num x))) ,
            h18
            )
            ))
          ( gcd/cost-next h h1 eqn2 h2 )
          ) in h19

gcd/body : (i : val gcd/i) →
        WfRec (lt/cost e/gcd gcd/cost) (const (cmp (F num))) i →
        cmp (F num)
gcd/body i1@(x , (y , h)) ih =
  ifz (const (F num)) y (ret {num} x)
  λ y' eqn →
    bind {mod-tp x y (suc≢0 eqn)} (F num) (mod x y (suc≢0 eqn)) λ { (z , eqn2) →
      let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
      ih (y , z , h2) (gcd/body/prf i1 y' eqn z eqn2)
  }

gcd/body-ext : (i : val gcd/i) →
      {IH IH' : WfRec (lt/cost e/gcd gcd/cost) (λ x → cmp (F num)) i} →
      (∀ {j} h → IH j h ≡ IH' j h) →
      gcd/body i IH ≡ gcd/body i IH'
gcd/body-ext i1@(x , y , h) ih-ext =
  P.cong (λ f → ifz (const (F num)) y (ret {num} x) f)
  (funext λ y' → funext λ eqn →
    P.cong (λ f → bind {mod-tp x y (suc≢0 eqn)} (F num) (mod x y (suc≢0 eqn)) f)
    (funext λ { (z , eqn2) →
      ih-ext ((gcd/body/prf i1 y' eqn z eqn2))}))

gcd/code : cmp (Π gcd/i λ _ → F num)
gcd/code (x , y , h) =
  All.wfRec (lt/cost/wf {gcd/i} {e/gcd} {gcd/cost})
  _ (const (cmp (F num))) gcd/body ((x , (y , h)))

gcd : cmp (Ψ gcd/i (λ { _ → num }) e/gcd gcd/cost)
gcd = gcd/code ,
  λ { (x , y , h) →
    iso.fwd ub⁻/decode
    (All.wfRec (lt/cost/wf {gcd/i} {e/gcd} {gcd/cost}) _
    (λ { (x , y , h)
        → ub num (gcd/code (x , y , h)) (gcd/cost (to-ext (x , y , h)))
    })
    ih ((x , y , h)))
  }
  where
  ih : (i : val gcd/i) → WfRec (lt/cost e/gcd gcd/cost)
       (λ i → ub num (gcd/code i) (gcd/cost (to-ext i))) i →
       ub num (gcd/code i) (gcd/cost (to-ext i))
  ih i@(x , y , h) Pi rewrite (FixPoint.unfold-wfRec (lt/cost/wf {gcd/i} {e/gcd} {gcd/cost})
             (const (cmp (F num)))
             gcd/body
             gcd/body-ext)
             {i}
          | gcd/cost-unfold' i
          = ub/ifz (const num) y (ret {num} x)
            (λ y' eqn →
             bind {mod-tp x y (suc≢0 eqn)} (F num) (mod x y (suc≢0 eqn)) λ { (z , eqn2) →
              let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
              (gcd/code) (y , z , h2)
             })
             0 (λ n' → suc (gcd/cost (suc n' , to-nat x % suc n' , m%n<n (to-nat x) n')))
             (ub/ret 0)
             λ y' eqn →
              ub/bind/suc
                {e = mod x y (suc≢0 eqn)}
                {f = λ { (z , eqn2) →
                  let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
                  (gcd/code) (y , z , h2)
                }}
                (e/mod-tp x y (suc≢0 eqn))
                (gcd/cost (suc (to-nat y') , to-nat x % suc (to-nat y') , m%n<n (to-nat x) (to-nat y')))
                mod/cost
                λ { (z , eqn2) →
                  let h2 = P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ (suc≢0 eqn)) in
                  let g = Pi (y , z , h2) (prf {x = x} {y' = y'} {h = h} eqn eqn2) in
                  let g1 = P.subst (λ i → ub num (gcd/code (y , z , h2)) (gcd/cost i))
                           (to-ext-unfold (y , z , h2)) g in
                  P.subst (λ i → ub num (gcd/code (y , z , h2)) (gcd/cost i))
                    (eqn3 {x} {y} {y'} {z} eqn eqn2) g1
                 }

              where
              prf : ∀ {x y y' z h} →
                        (eqn : suc (to-nat y') ≡ to-nat y) →
                        (eqn2 : to-nat z ≡ _%_ (to-nat x) (to-nat y) {suc≢0 eqn}) →
                        let h1 = suc≢0 eqn in
                        gcd/cost (to-ext (y , z , P.subst (λ k → suc k ≤ to-nat y) (symm eqn2) (m%n<n' _ _ h1))) <
                                           (if {const ℕ} (to-nat y) 0 (λ y' → suc
                                           (gcd/cost (suc y' , to-nat x % suc y' , m%n<n (to-nat x) y'))))
              prf {x} {y} {y'} {z} {h} eqn eqn2 rewrite symm (gcd/cost-unfold' (x , y , h)) =
                  gcd/body/prf (x , y , h) y' eqn z eqn2

              eqn3 : ∀ {x y y' z} →
                        (eqn : suc (to-nat y') ≡ to-nat y) →
                        (eqn2 : to-nat z ≡ _%_ (to-nat x) (to-nat y) {suc≢0 eqn}) →
                        let h1 = suc≢0 eqn in
                        _≡_ {A = m>n}
                          (to-nat y , to-nat z , P.subst (λ k → suc k ≤ to-nat y) (symm eqn2)
                          (m%n<n' (to-nat x) (to-nat y) (suc≢0 eqn)))
                          (suc (to-nat y') ,
                            to-nat x % (suc (to-nat y')), m%n<n (to-nat x) (to-nat y'))
              eqn3 {x} {y} {y'} {z} eqn eqn2 =
                   let eqn3 = P.subst (λ yy → (h : suc (to-nat y') ≡ yy) → to-nat z ≡ _%_ (to-nat x) yy {P.subst (λ n → False (n ≟ 0)) h tt}) (symm eqn)
                             (λ h → P.subst (λ eqn → to-nat z ≡ _%_ (to-nat x) (to-nat y) {P.subst (λ n → False (n ≟ 0)) eqn tt}) (uip eqn h) eqn2)
                             refl in
                    Inverse.f Σ-≡,≡↔≡ (
                      symm eqn , Inverse.f Σ-≡,≡↔≡ (
                        P.trans (fst/subst (symm eqn))
                          (P.trans eqn3 refl) ,
                          ≤-irrelevant _ _))
