{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Eq
open import Data.Nat as Nat
open import Connectives renaming (_⇒_[_,_] to Ψ)
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



mod-tp : (x y : val num) → (cmp (meta (False (to-nat y ≟ 0)))) → tp pos
mod-tp x y h = Σ++ num λ z → (U (meta (to-nat z ≡ _%_ (to-nat x) (to-nat y) {h})))

e/mod-tp : (x y : val num) → (h : cmp (meta (False (to-nat y ≟ 0)))) → Ext (mod-tp x y h)
e/mod-tp x y h = e/pair e/num (λ z → e/meta (to-nat z ≡ _%_ (to-nat x) (to-nat y) {h}))

postulate 
  mod : cmp (
          Π num λ x → 
          Π num λ y → 
          Π (U (meta (False (to-nat y ≟ 0)))) λ h → 
          F (mod-tp x y h))
  
  -- mod/coh : ∀ {x y} → (h : False (to-nat y ≟ 0)) → 
            -- bind {num} (F nat) (mod x y h) to-nat ≡ (_%_ (to-nat x) (to-nat y) {h})

  mod/cost : ∀ {x y h} → ub (mod-tp x y h) (mod x y h) 1

m>n = Σ ℕ λ m → Σ ℕ λ n → (m > n)

gcd/cost/helper : ∀ n → ((m : ℕ) → m < n → (k : ℕ) → (k > m) → ℕ) → (m : ℕ) → (m > n) → ℕ
gcd/cost/helper zero h m h' = zero 
gcd/cost/helper n@(suc n') h m h' = suc (h (m % n) (m%n<n m n') n (m%n<n m n'))

gcd/cost : m>n → ℕ 
gcd/cost (x , (y , g)) = All.wfRec <-wellFounded _ (λ y → (x : ℕ) → x > y → ℕ) 
  gcd/cost/helper y x g

all-to-some : ∀ {a ℓ r} {A : Set a} {_<_ : Rel A r} {P : Pred A ℓ} {f x} (wf : WellFounded _<_) → 
              All.wfRecBuilder wf ℓ P f x ≡ Some.wfRecBuilder P f x (wf x) 
all-to-some wf = refl

gcd/cost/helper-ext : (x₁ : ℕ)
    {IH IH′ : WfRec _<_ (λ y₁ → (x₂ : ℕ) → x₂ > y₁ → ℕ) x₁} →
    ({y = y₁ : ℕ} (y<x : y₁ < x₁) → IH y₁ y<x ≡ IH′ y₁ y<x) →
    gcd/cost/helper x₁ IH ≡ gcd/cost/helper x₁ IH′ 
gcd/cost/helper-ext zero h = refl
gcd/cost/helper-ext (suc x) h = 
  funext λ m → funext λ h1 → P.cong suc (
    let g = h {m % suc x} (m%n<n m x) in 
    P.cong-app (P.cong-app g _) _
  )


module irr
  {a r ℓ}
  {A : Set a}
  {_<_ : Rel A r} (wf : WellFounded _<_)
  (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P)
  (f-ext : (x : A) {IH IH′ : WfRec _<_ P x} → (∀ {y} y<x → IH y y<x ≡ IH′ y y<x) → f x IH ≡ f x IH′)
  where

  some-wfRecBuilder-irrelevant : ∀ x → (q q′ : Acc _<_ x) → Some.wfRecBuilder P f x q ≡ Some.wfRecBuilder P f x q′
  some-wfRecBuilder-irrelevant = All.wfRec wf _ 
                                  ((λ x → (q q′ : Acc _<_ x) → Some.wfRecBuilder P f x q ≡ Some.wfRecBuilder P f x q′)) 
                                  ((λ { x IH (acc rs) (acc rs') → funext λ y → funext λ h → f-ext y λ {y'} h' → 
                                    let g = IH y h (rs y h) (rs' y h) in 
                                    P.cong-app (P.cong-app g y') h'
                                  }))

gcd/cost-unfold-zero : ∀ {x h} → gcd/cost (x , zero , h) ≡ zero
gcd/cost-unfold-zero = refl

gcd/cost-unfold-suc : ∀ {x y h} → gcd/cost (x , suc y , h) ≡ 
                              suc (gcd/cost (suc y , x % suc y , m%n<n x y)) 
gcd/cost-unfold-suc {x} {y} {h} = P.cong suc 
  ( P.subst (λ  ih → 
      gcd/cost/helper (mod-helper 0 y x y) (ih) (suc y) (m%n<n x y) ≡
        gcd/cost/helper (mod-helper 0 y x y) 
        (All.wfRecBuilder <-wellFounded L.zero
        (λ y₁ → (x₁ : ℕ) → x₁ > y₁ → ℕ) gcd/cost/helper
        (mod-helper 0 y x y))
        (suc y) (m%n<n x y)) 
    (P.trans (all-to-some {f = gcd/cost/helper} <-wellFounded) 
    (irr.some-wfRecBuilder-irrelevant <-wellFounded (λ y → (x : ℕ) → x > y → ℕ) 
      gcd/cost/helper (gcd/cost/helper-ext) (x % suc y) 
      (<-wellFounded (mod-helper 0 y x y)) 
      (Subrelation.accessible ≤⇒≤′
     (Data.Nat.Induction.<′-wellFounded′ (suc y)
      (mod-helper 0 y x y) (≤⇒≤′ (m%n<n x y)))))
    ) 
    refl
  )

gcd/cost-unfold : ∀ {x y h} → gcd/cost (x , y , h) ≡ if {λ _ → ℕ} y zero (λ y' → suc (gcd/cost (suc y' , x % suc y' , m%n<n x y')))
gcd/cost-unfold {x} {zero} {h} = refl
gcd/cost-unfold {x} {suc y'} {h} = gcd/cost-unfold-suc {x} {y'} {h}

gcd/i = Σ++ num λ x → Σ++ num λ y → U (meta (to-nat x > to-nat y)) 

e/gcd : Ext gcd/i
e/gcd = e/pair e/num (λ x → e/pair e/num (λ y → e/meta (to-nat x > to-nat y)))

to-ext = iso.fwd (Ext.rep e/gcd)

fst/subst : ∀ {a b} {A B : Set a} {C : A → B → Set b} {x y : A} {p : Σ B (λ b → C x b)} (e : x ≡ y) → 
            fst (P.subst (λ x → Σ B (λ b → C x b)) e p) ≡ fst p
fst/subst refl = refl

snd/subst : ∀ {a b} {A B : Set a} {C : A → B → Set b} {x y : A} {p : Σ B (λ b → C x b)} (e : x ≡ y) → 
            snd (P.subst (λ x → Σ B (λ b → C x b)) e p) ≡ 
            P.subst (λ b → C y b) (symm (fst/subst e)) (P.subst (λ x → C x (fst p)) e (snd p))
snd/subst refl = refl

to-ext-unfold : ∀ (i@(x , y , h) : val gcd/i) → to-ext (x , y , h) ≡ (to-nat x , to-nat y , h)
to-ext-unfold i@(x , y , h) = 
  Inverse.f Σ-≡,≡↔≡ (refl , Inverse.f Σ-≡,≡↔≡ 
    (fst/subst (symm (nat-num x)) , ≅-to-≡ 
      (H.trans (≡-subst-removable ((λ a → Ext.Carrier (e/meta  (to-nat (iso.bwd (Ext.rep e/num) (to-nat x)) > to-nat (iso.bwd (Ext.rep e/num) a))))) 
      ((fst/subst (symm (nat-num x)))) (snd    (P.subst     (λ a →        Ext.Carrier        (e/pair e/num         (λ y₁ → e/meta (to-nat (iso.bwd (Ext.rep e/num) a) > to-nat y₁))))
           refl (snd (to-ext (x , y , h)))))) 
      (let g = snd/subst {C = λ x n → n < to-nat x} {p = (to-nat y ,
                                  P.subst (λ a → suc (to-nat a) ≤ to-nat x) (symm (nat-num y)) h)} 
                                  (symm (nat-num x)) in
                                   H.trans (≡-to-≅ g) 
                                   (H.trans 
                                   (H.trans (≡-subst-removable ((λ n → n < to-nat (to-num (to-nat x)))) 
                                   ((symm (fst/subst (symm (nat-num x))))) 
                                   ((P.subst (λ x₁ → to-nat y < to-nat x₁) (symm (nat-num x))
                                   (P.subst (λ a → suc (to-nat a) ≤ to-nat x) (symm (nat-num y)) h)))) 
                                   (≡-subst-removable (λ x₁ → to-nat y < to-nat x₁) (symm (nat-num x)) (P.subst (λ a → suc (to-nat a) ≤ to-nat x) (symm (nat-num y)) h))) 
                                   (≡-subst-removable (λ a → suc (to-nat a) ≤ to-nat x) (symm (nat-num y)) h))))))

gcd/cost-unfold' : ∀ (i@(x , y , h) : val gcd/i) → gcd/cost (to-ext i) ≡
                      if {λ _ → ℕ} (to-nat y) zero 
                      (λ y' → suc (gcd/cost (suc y' , to-nat x % suc y' , m%n<n (to-nat x) y')))
gcd/cost-unfold' i@(x , y , h) rewrite symm (gcd/cost-unfold {to-nat x} {to-nat y} {h}) = 
  P.cong gcd/cost {x = to-ext i} {y = (to-nat x , to-nat y , h)} 
  (Inverse.f Σ-≡,≡↔≡ (refl , 
    Inverse.f Σ-≡,≡↔≡ (fst/subst (symm (nat-num x)) , 
    ≅-to-≡  
      ( H.trans  
      (≡-subst-removable (_>_ (to-nat x)) ((fst/subst (symm (nat-num x)))) 
      ((snd
     (P.subst
      (λ a →
         Ext.Carrier (e/pair e/num (λ y₁ → e/meta (to-nat a > to-nat y₁))))
      (symm (nat-num x))
      (iso.fwd
       (Ext.rep (e/pair e/num (λ y₁ → e/meta (to-nat x > to-nat y₁))))
       (y , h))))))
        (let g = ≡-subst-removable (λ a →
                    Ext.Carrier (e/pair e/num (λ y₁ → e/meta (to-nat a > to-nat y₁))))
                (symm (nat-num x))
                (iso.fwd
                  (Ext.rep (e/pair e/num (λ y₁ → e/meta (to-nat x > to-nat y₁))))
                  (y , h)) in 
         let g1 = H.cong snd g in
         let g2 = ≡-subst-removable (λ a → suc (to-nat a) ≤ to-nat x) (symm (nat-num y)) h in
          H.trans g1 g2)
       ))))

m%n<n' : ∀ m n h → _%_ m n {h} < n
m%n<n' m (suc n) h = m%n<n m n

gcd/cost-next' : ∀ {x y z} → (h1 : False (y ≟ 0)) → (h : x > y) → (g : z ≡ _%_ x y {h1}) → (h3 : y > z) → gcd/cost (x , y , h) > gcd/cost (y , x % y , P.subst (_>_ y) g h3)
gcd/cost-next' {zero} h1 h g h3 = case h of λ { () }
gcd/cost-next' {suc x'} {zero} h1 h g h3 = case h3 of λ { () }
gcd/cost-next' {suc x'} {suc y'} h1 h g h3 rewrite gcd/cost-unfold-suc {suc x'} {y'} {h} = 
  ≤-reflexive (P.cong suc
      (P.cong (gcd/cost/helper (mod-helper 0 y' (suc x') y')
      (λ y y<x → gcd/cost/helper y
      (Some.wfRecBuilder (λ y₁ → (x : ℕ) → suc y₁ ≤ x → ℕ)
      gcd/cost/helper y
      (Subrelation.accessible ≤⇒≤′
      (Data.Nat.Induction.<′-wellFounded′ (mod-helper 0 y' (suc x') y') y
      (≤⇒≤′ y<x)))))
      (suc y')) 
  (<-irrelevant (P.subst (λ n → suc n ≤ suc y') g h3) (s≤s (Data.Nat.DivMod.Core.a[modₕ]n<n 0 (suc x') y')))
   ))

gcd/cost-next : ∀ {x y z} → (h : x > y) → (h1 : False (y ≟ 0)) → (h2 : z ≡ _%_ x y {h1}) → 
                (h3 : y > z) → 
                gcd/cost (x , (y , h)) > gcd/cost (y , (z , h3))
gcd/cost-next {x} {y} {z} h h1 h2 h3 = 
  let h4 : ∀ {n} → z ≡ n → y > n 
      h4 = λ h → P.subst (λ n → y > n) h h3 in 
  P.subst (λ n → 
            (g : z ≡ n) → gcd/cost (x , (y , h)) > gcd/cost (y , (n , P.subst (λ n → y > n) g h3))) (symm h2) 
            (λ g → gcd/cost-next' h1 h h2 h3) 
            refl

suc≢0 : ∀ {n m} → suc n ≡ m → False (m ≟ 0)
suc≢0 h = P.subst (λ n → False (n ≟ 0)) h tt 

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