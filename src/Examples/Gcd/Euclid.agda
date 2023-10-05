{-# OPTIONS --rewriting #-}

module Examples.Gcd.Euclid where

open import Algebra.Cost

{- This file defines the parameters of the analysis of Euclid's algorithm for gcd
   and its cost recurrence relation. -}
open import Calf ℕ-CostMonoid
open import Calf.Data.Nat using (nat)
open import Data.Nat
open import Relation.Binary.PropositionalEquality as P
open import Induction.WellFounded
open import Induction
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Nat.Induction using (<-wellFounded)
open import Agda.Builtin.Nat using (div-helper; mod-helper)
open import Relation.Binary using (Rel)
open import Relation.Unary using (Pred; _⊆′_)

mod-tp : (x y : val nat) → False (y ≟ 0) → tp⁺
mod-tp x y h = Σ⁺ nat λ z → meta⁺ (z ≡ _%_ x y {{≢-nonZero (toWitnessFalse h)}})

mod : cmp (
        Π nat λ x →
        Π nat λ y →
        Π (meta⁺ (False (y ≟ 0))) λ h →
        F (mod-tp x y h))
mod x y h = step (F (mod-tp x y h)) 1 (ret {mod-tp x y h} (_%_  x y {{≢-nonZero (toWitnessFalse h)}} , refl))


gcd/depth/helper : ∀ n → ((m : ℕ) → m < n → (k : ℕ) → (k > m) → ℕ) → (m : ℕ) → (m > n) → ℕ
gcd/depth/helper zero h m h' = 0
gcd/depth/helper n@(suc _) h m h' = suc (h (m % n) (m%n<n m n) n (m%n<n m n))

gcd/i = Σ⁺ nat λ x → Σ⁺ nat λ y → meta⁺ (x > y)
m>n = val gcd/i

gcd/depth : m>n → ℕ
gcd/depth (x , (y , g)) = All.wfRec <-wellFounded _ (λ y → (x : ℕ) → x > y → ℕ)
  gcd/depth/helper y x g

gcd/depth/helper-ext : (x₁ : ℕ)
    {IH IH′ : WfRec _<_ (λ y₁ → (x₂ : ℕ) → x₂ > y₁ → ℕ) x₁} →
    ({y = y₁ : ℕ} (y<x : y₁ < x₁) → IH y₁ y<x ≡ IH′ y₁ y<x) →
    gcd/depth/helper x₁ IH ≡ gcd/depth/helper x₁ IH′
gcd/depth/helper-ext zero h = refl
gcd/depth/helper-ext x@(suc _) h =
  funext λ m → funext λ h1 → P.cong suc (
    let g = h {m % x} (m%n<n m x) in
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

gcd/depth-unfold-zero : ∀ {x h} → gcd/depth (x , 0 , h) ≡ 0
gcd/depth-unfold-zero = refl

gcd/depth-unfold-suc : ∀ {x y} {{_ : NonZero y}} {h} → gcd/depth (x , y , h) ≡
                              suc (gcd/depth (y , x % y , m%n<n x y))
gcd/depth-unfold-suc {x} {y@(suc y')} {h} = P.cong suc
  ( P.subst (λ ih →
      gcd/depth/helper (mod-helper 0 y' x y') ih y (m%n<n x y) ≡
        gcd/depth/helper (mod-helper 0 y' x y')
        (All.wfRecBuilder <-wellFounded _
        (λ y₁ → (x₁ : ℕ) → x₁ > y₁ → ℕ) gcd/depth/helper
        (mod-helper 0 y' x y'))
        y (m%n<n x y))
    (irr.some-wfRecBuilder-irrelevant <-wellFounded (λ y → (x : ℕ) → x > y → ℕ)
      gcd/depth/helper (gcd/depth/helper-ext) (x % y)
      (<-wellFounded (mod-helper 0 y' x y'))
      (Subrelation.accessible <⇒<′
     (Data.Nat.Induction.<′-wellFounded′ y
      (mod-helper 0 y' x y') (<⇒<′ (m%n<n x y)))))
    refl
  )
