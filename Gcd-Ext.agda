
{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import Num
open import PhaseDistinction
open import Connectives
open import Refinement
open import Upper
open import Eq

open import Gcd
open import Gcd-direct
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

-- mathematical specification of the greatest common divisor (gcd)
gcd/spec : m>n → ℕ
gcd/spec (m , (n , h)) = gcd′ m n (<-wellFounded m) h

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

gcd/spec-unfold : ∀ {x y h} → gcd/spec (x , y , h) ≡
                        if {const ℕ} y x (λ y' → gcd/spec (suc y' , x % suc y' , m%n<n x y'))
gcd/spec-unfold {x} {zero} {h} = refl
gcd/spec-unfold {x} {y@(suc y')} {h} = gcd′-ext {m = suc y'} {n = x % suc y'}

gcd/cost≡zero : ∀ {x y h} → gcd/cost (x , y , h) ≡ zero → y ≡ zero
gcd/cost≡zero {x} {zero} {h} = λ _ → refl

m>n/irrelevant : ∀ {x1 x2 y1 y2 h1 h2} → (x1 ≡ x2) → (y1 ≡ y2) → _≡_ {A = m>n} (x1 , y1 , h1) (x2 , y2 , h2)
m>n/irrelevant refl refl = Inverse.f Σ-≡,≡↔≡ (refl , Inverse.f Σ-≡,≡↔≡ (refl , ≤-irrelevant _ _))

≤-suc : ∀ {m n} → suc m ≥ suc n → m ≥ n
≤-suc {m} {n} h =
    let h1 : m + 1 ≥ n + 1
        h1 = P.subst₂ (λ m n → m ≥ n)
          (P.sym (P.trans (+-suc m 0) (P.cong suc (+-identityʳ m))))
          (P.sym (P.trans (+-suc n 0) (P.cong suc (+-identityʳ n))))
          h
    in +-cancelʳ-≤ n m h1

-- the explicitly clocked version also satisfy the specification, given that we
-- start with enough time on the clock
gcd/clocked≡gcd/spec : ∀ k x y h → k ≥ gcd/cost (to-ext (x , y , h)) →
    ◯ (gcd/clocked k (x , y , h) ≡ ret {num} (to-num (gcd/spec (to-nat x , to-nat y , h))))
gcd/clocked≡gcd/spec zero x y h h1 =
  let h1' = P.subst (λ n → zero ≥ gcd/cost n) (to-ext-unfold (x , y , h)) h1 in
  let h2 = n≤0⇒n≡0 h1' in
  let h3 = gcd/cost≡zero {h = h} h2 in
  P.subst (λ y → (h : to-nat x > y) → ◯ (ret {num} x ≡ ret {num} (to-num (gcd/spec (to-nat x , y , h))))) (symm h3)
  (λ _ _ → refl) h
gcd/clocked≡gcd/spec (suc k) x y h h1 u =
  ifz (λ n → meta (to-nat y ≡ n → P (to-num n))) y
  (λ h h'' u  → refl)
  (λ y' h' eqn h'' u →
  let h1' = P.subst (λ n → suc k ≥ gcd/cost n) (to-ext-unfold (x , y , h)) h1 in
  let h2 = P.subst (λ n → (h : to-nat x > n) → suc k ≥ gcd/cost (to-nat x , n , h)) eqn
        (λ _ → h1') (subst (λ k → to-nat x > k) eqn h)  in
  let h3 = P.subst (λ i → suc k ≥ gcd/cost i)
            (m>n/irrelevant {x1 = to-nat x} {y1 = suc (to-nat y')} {h1 = subst (λ k → to-nat x > k) eqn h} {h2 = h''} refl refl) h2 in
  i/suc {y'} {y} {x} {h''} u h' h3)
  refl h u

  where
      P = (λ y → ∀ h → ◯ (gcd/clocked (suc k) (x , y , h) ≡
                            ret {num} (to-num (gcd/spec (to-nat x , to-nat y , h)))))

      i/suc : ∀ {y' y x h} →
          ext →
          suc (to-nat y') ≡ to-nat y →
          suc k ≥ gcd/cost (to-nat x , suc (to-nat y') , h) →
        gcd/clocked (suc k) (x , to-num (suc (to-nat y')) , h) ≡
        ret {num} (to-num (gcd/spec (to-nat x , suc (to-nat y') , h)))
      i/suc {y'} {y} {x} {h} u y'+1≡y k≥cost with mod/cost {x} {to-num (suc (to-nat y'))} {tt}
      ... | (ub/intro {q = q} (z , eqn2) bound eqn) with  mod x (to-num (suc (to-nat y'))) tt  | eq/ref eqn
      ... | _ | refl with step' (F num) q
                          (gcd/clocked k (to-num (suc (to-nat y')) , z ,
                          P.subst (λ k → suc k ≤ suc (to-nat y')) (symm eqn2) (m%n<n' (to-nat x) _ tt))) |  step'/ext (F num)
                          (gcd/clocked k (to-num (suc (to-nat y')) , z ,
                          P.subst (λ k → suc k ≤ suc (to-nat y')) (symm eqn2) (m%n<n' (to-nat x) _ tt))) q u
      ... | _ | refl =
           let h2 = P.subst (λ k → suc k ≤ suc (to-nat y')) (symm eqn2) (m%n<n' (to-nat x) _ tt) in
           let h3 = P.subst (λ n → suc k ≥ n) (gcd/cost-unfold-suc {to-nat x} {to-nat y'} {h}) k≥cost in
           let h4 = ≤-suc h3 in

           let h5 = gcd/clocked≡gcd/spec k (to-num (suc (to-nat y'))) z h2
                    (subst (λ i → k ≥ gcd/cost i) (symm (to-ext-unfold (to-num (suc (to-nat y')) , z , h2)))
                    (P.subst (λ i → k ≥ gcd/cost i)
                    (m>n/irrelevant {h1 = m%n<n (to-nat x) (to-nat y')} {h2 = h2} refl (symm eqn2)) h4)) u in
          let h4 : _≡_ {A = m>n} (suc (to-nat y') , to-nat z , h2) (suc (to-nat y') , to-nat x % suc (to-nat y') , m%n<n' (to-nat x) _ tt)
              h4 = m>n/irrelevant refl eqn2 in
           P.trans h5 (P.cong (ret {num} ∘ to-num)
              (gcd′-ext' h4 ))

id≥gcd/cost : ∀ x y h → to-nat y ≥ gcd/cost (to-ext (x , y , h))
id≥gcd/cost x y h = subst (λ i → to-nat y ≥ gcd/cost i)
  (symm (to-ext-unfold (x , y , h)))
  (g _ _ h)
   where
   g : ∀ n m → (h : m > n) → n ≥ gcd/cost (m , n , h)
   g n = All.wfRec <-wellFounded _ (λ n → ∀ m → (h : m > n) → n ≥ gcd/cost (m , n , h))
          (λ n →
            let g = (case n return (λ n →
                    WfRec _<_ (λ n₂ → (m₁ : ℕ) (h₂ : m₁ > n₂) → n₂ ≥ gcd/cost (m₁ , n₂ , h₂)) n →
                    ∀ m → (h : m > n) → n ≥ gcd/cost (m , n , h)) of λ {
                  (zero) → λ ih _ _ → ≤-reflexive refl
                  ; (suc n') → λ ih m h' → subst (λ k → suc n' ≥ k) (symm (gcd/cost-unfold-suc {m} {n'} {h'}))
                      ( let g1 = ih (m % suc n') (m%n<n m n') (suc n') (m%n<n m n') in
                      <-transʳ g1 (m%n<n m n'))
                  })
            in
            λ ih m h → g ih m h
           ) n

-- computing the clock is fast since it's just projecting the argument
gcd/fast : cmp (Π gcd/i λ _ → F num)
gcd/fast i@(x , y , h) = gcd/clocked (to-nat y) i

-- the clock is safe w.r.t specification of gcd
gcd/fast≡gcd/spec : ∀ x y h → ◯ (gcd/fast (x , y , h) ≡ ret {num} (to-num (gcd/spec (to-nat x , to-nat y , h))))
gcd/fast≡gcd/spec x y h = gcd/clocked≡gcd/spec (to-nat y) x y h (id≥gcd/cost x y h)