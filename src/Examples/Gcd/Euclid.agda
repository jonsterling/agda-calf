{-# OPTIONS --prop --rewriting #-}

module Examples.Gcd.Euclid where

{- This file defines the parameters of the analysis of Euclid's algorithm for gcd
   and its cost recurrence relation. -}
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

mod-tp : (x y : val nat) → cmp (meta (False (toℕ y ≟ 0))) → tp pos
mod-tp x y h = Σ++ nat λ z → (U (meta (toℕ z ≡ _%_ (toℕ x) (toℕ y) {h})))

mod : cmp (
        Π nat λ x →
        Π nat λ y →
        Π (U (meta (False (toℕ y ≟ 0)))) λ h →
        F (mod-tp x y h))
mod x y h = step' (F (mod-tp x y h)) 1 (ret {mod-tp x y h} (tonat (_%_ (toℕ x) (toℕ y) {h}) , refl))

e/mod-tp : (x y : val nat) → (h : cmp (meta (False (toℕ y ≟ 0)))) → Ext (mod-tp x y h)
e/mod-tp x y h = e/pair e/nat (λ z → e/meta (toℕ z ≡ _%_ (toℕ x) (toℕ y) {h}))

m>n = Σ ℕ λ m → Σ ℕ λ n → (m > n)

gcd/cost/helper : ∀ n → ((m : ℕ) → m < n → (k : ℕ) → (k > m) → ℕ) → (m : ℕ) → (m > n) → ℕ
gcd/cost/helper zero h m h' = 0
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

gcd/cost-unfold-zero : ∀ {x h} → gcd/cost (x , 0 , h) ≡ 0
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

gcd/cost-unfold : ∀ {x y h} → gcd/cost (x , y , h) ≡ if {λ _ → ℕ} y 0 (λ y' → suc (gcd/cost (suc y' , x % suc y' , m%n<n x y')))
gcd/cost-unfold {x} {zero} {h} = refl
gcd/cost-unfold {x} {suc y'} {h} = gcd/cost-unfold-suc {x} {y'} {h}

gcd/i = Σ++ nat λ x → Σ++ nat λ y → U (meta (toℕ x > toℕ y))

e/gcd : Ext gcd/i
e/gcd = e/pair e/nat (λ x → e/pair e/nat (λ y → e/meta (toℕ x > toℕ y)))

to-ext = iso.fwd (Ext.rep e/gcd)

fst/subst : ∀ {a b} {A B : Set a} {C : A → B → Set b} {x y : A} {p : Σ B (λ b → C x b)} (e : x ≡ y) →
            fst (P.subst (λ x → Σ B (λ b → C x b)) e p) ≡ fst p
fst/subst refl = refl

snd/subst : ∀ {a b} {A B : Set a} {C : A → B → Set b} {x y : A} {p : Σ B (λ b → C x b)} (e : x ≡ y) →
            snd (P.subst (λ x → Σ B (λ b → C x b)) e p) ≡
            P.subst (λ b → C y b) (P.sym (fst/subst e)) (P.subst (λ x → C x (fst p)) e (snd p))
snd/subst refl = refl

to-ext-unfold : ∀ (i@(x , y , h) : val gcd/i) → to-ext (x , y , h) ≡ (toℕ x , toℕ y , h)
to-ext-unfold i@(x , y , h) =
  Inverse.f Σ-≡,≡↔≡ (refl , Inverse.f Σ-≡,≡↔≡
    (fst/subst (P.sym ( ℕ-nat x)) , ≅-to-≡
      (H.trans (≡-subst-removable ((λ a → Ext.Carrier (e/meta  (toℕ (iso.bwd (Ext.rep e/nat) (toℕ x)) > toℕ (iso.bwd (Ext.rep e/nat) a)))))
      ((fst/subst (P.sym ( ℕ-nat x)))) (snd    (P.subst     (λ a →        Ext.Carrier        (e/pair e/nat         (λ y₁ → e/meta (toℕ (iso.bwd (Ext.rep e/nat) a) > toℕ y₁))))
           refl (snd (to-ext (x , y , h))))))
      (let g = snd/subst {C = λ x n → n < toℕ x} {p = (toℕ y ,
                                  P.subst (λ a → suc (toℕ a) ≤ toℕ x) (P.sym ( ℕ-nat y)) h)}
                                  (P.sym ( ℕ-nat x)) in
                                   H.trans (≡-to-≅ g)
                                   (H.trans
                                   (H.trans (≡-subst-removable ((λ n → n <  (toℕ x)))
                                   ((P.sym (fst/subst (P.sym ( ℕ-nat x)))))
                                   ((P.subst (λ x₁ → toℕ y < toℕ x₁) (P.sym ( ℕ-nat x))
                                   (P.subst (λ a → suc (toℕ a) ≤ toℕ x) (P.sym ( ℕ-nat y)) h))))
                                   (≡-subst-removable (λ x₁ → toℕ y < toℕ x₁) (P.sym ( ℕ-nat x)) (P.subst (λ a → suc (toℕ a) ≤ toℕ x) (P.sym ( ℕ-nat y)) h)))
                                   (≡-subst-removable (λ a → suc (toℕ a) ≤ toℕ x) (P.sym ( ℕ-nat y)) h))))))

gcd/cost-unfold' : ∀ (i@(x , y , h) : val gcd/i) → gcd/cost (to-ext i) ≡
                      if {λ _ → ℕ} (toℕ y) 0
                      (λ y' → suc (gcd/cost (suc y' , toℕ x % suc y' , m%n<n (toℕ x) y')))
gcd/cost-unfold' i@(x , y , h) rewrite P.sym (gcd/cost-unfold {toℕ x} {toℕ y} {h}) =
  P.cong gcd/cost {x = to-ext i} {y = (toℕ x , toℕ y , h)}
  (Inverse.f Σ-≡,≡↔≡ (refl ,
    Inverse.f Σ-≡,≡↔≡ (fst/subst (P.sym ( ℕ-nat x)) ,
    ≅-to-≡
      ( H.trans
      (≡-subst-removable (_>_ (toℕ x)) ((fst/subst (P.sym ( ℕ-nat x))))
      ((snd
     (P.subst
      (λ a →
         Ext.Carrier (e/pair e/nat (λ y₁ → e/meta (toℕ a > toℕ y₁))))
      (P.sym ( ℕ-nat x))
      (iso.fwd
       (Ext.rep (e/pair e/nat (λ y₁ → e/meta (toℕ x > toℕ y₁))))
       (y , h))))))
        (let g = ≡-subst-removable (λ a →
                    Ext.Carrier (e/pair e/nat (λ y₁ → e/meta (toℕ a > toℕ y₁))))
                (P.sym ( ℕ-nat x))
                (iso.fwd
                  (Ext.rep (e/pair e/nat (λ y₁ → e/meta (toℕ x > toℕ y₁))))
                  (y , h)) in
         let g1 = H.cong snd g in
         let g2 = ≡-subst-removable (λ a → suc (toℕ a) ≤ toℕ x) (P.sym ( ℕ-nat y)) h in
          H.trans g1 g2)
       ))))

m%n<n' : ∀ m n h → _%_ m n {h} < n
m%n<n' m (suc n) h = m%n<n m n

suc≢0 : ∀ {n m} → suc n ≡ m → False (m ≟ 0)
suc≢0 h = P.subst (λ n → False (n ≟ 0)) h tt
