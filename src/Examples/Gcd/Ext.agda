{-# OPTIONS --prop --rewriting #-}

module Examples.Gcd.Ext where

open import Calf.CostMonoid
import Calf.CostMonoids as CM

open import Calf CM.ℕ-CostMonoid
open import Calf.Types.Nat CM.ℕ-CostMonoid as Nat

open import Examples.Gcd.Euclid
open import Examples.Gcd.Clocked

open import Data.Nat.GCD
open import Data.Nat.DivMod
open import Data.Nat
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality as P
open import Induction.WellFounded
open import Relation.Binary.Construct.On as On
open import Function.Base using (_on_)
open import Function
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Product
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

gcd/cost≡zero : ∀ {x y h} → gcd/cost (x , y , h) ≡ 0 → y ≡ 0
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
    ◯ (gcd/clocked k (x , y , h) ≡ ret {nat} (tonat (gcd/spec (toℕ x , toℕ y , h))))
gcd/clocked≡gcd/spec zero x y h h1 =
  let h1' = P.subst (λ n → 0 ≥ gcd/cost n) (to-ext-unfold (x , y , h)) h1 in
  let h2 = n≤0⇒n≡0 h1' in
  let h3 = gcd/cost≡zero {h = h} h2 in
  P.subst (λ y → (h : toℕ x > y) → ◯ (ret {nat} x ≡ ret {nat} (tonat (gcd/spec (toℕ x , y , h))))) (P.sym h3)
  (λ _ _ → refl) h
gcd/clocked≡gcd/spec (suc k) x y h h1 u =
  Nat.rec y (λ y → meta (P y))
  (λ _ _  → refl)
  (λ y' _ h h1 →
  let h2 = P.subst (λ n → suc k ≥ gcd/cost n) (to-ext-unfold (x , succ y' , h)) h1 in
  let h3 = P.subst (λ n → suc k ≥ n) (gcd/cost-unfold-suc {toℕ x} {toℕ y'} {h}) h2 in
  let h4 = ≤-suc h3 in
  let i' = (succ y' , tonat (toℕ x % toℕ (succ y')) , m%n<n (toℕ x) (toℕ y')) in
  let g = gcd/clocked≡gcd/spec k (succ y') (tonat (toℕ x % toℕ (succ y'))) (m%n<n (toℕ x) (toℕ y')) in
  let g' = P.subst (λ i → k ≥ gcd/cost i → ◯ (gcd/clocked k i' ≡ ret {nat} (tonat (gcd/spec (toℕ (succ y') , toℕ x % toℕ (succ y') , m%n<n (toℕ x) (toℕ y')))))) (to-ext-unfold i') g in
  let h5 = g' h4 u in
  begin
  gcd/clocked (suc k) (x , succ y' , h) ≡⟨ refl ⟩
  step' (F nat) 1 (gcd/clocked k (succ y' , tonat (toℕ x % toℕ (succ y')) , m%n<n (toℕ x) (toℕ y'))) ≡⟨ step'/ext (F nat) (gcd/clocked k (succ y' , tonat (toℕ x % toℕ (succ y')) , m%n<n (toℕ x) (toℕ y'))) 1 u ⟩
  gcd/clocked k (succ y' , tonat (toℕ x % toℕ (succ y')) , m%n<n (toℕ x) (toℕ y')) ≡⟨ h5 ⟩
  ret (tonat (gcd/spec (toℕ (succ y') , toℕ x % toℕ (succ y') , m%n<n (toℕ x) (toℕ y')))) ≡⟨ P.cong (λ x → ret (tonat x)) (P.sym (gcd/spec-unfold {toℕ x} {toℕ (succ y')} {h})) ⟩
  ret (tonat (gcd/spec (toℕ x , toℕ (succ y') , h)))
  ∎
  )
  h h1

  where
      P = (λ y → ∀ h → (suc k ≥ gcd/cost (to-ext (x , y , h))) →  gcd/clocked (suc k) (x , y , h) ≡
                            ret {nat} (tonat (gcd/spec (toℕ x , toℕ y , h))))
      open ≡-Reasoning

id≥gcd/cost : ∀ x y h → toℕ y ≥ gcd/cost (to-ext (x , y , h))
id≥gcd/cost x y h = subst (λ i → toℕ y ≥ gcd/cost i)
  (P.sym (to-ext-unfold (x , y , h)))
  (g _ _ h)
   where
   g : ∀ n m → (h : m > n) → n ≥ gcd/cost (m , n , h)
   g n = All.wfRec <-wellFounded _ (λ n → ∀ m → (h : m > n) → n ≥ gcd/cost (m , n , h))
          (λ n →
            let g = (case n return (λ n →
                    WfRec _<_ (λ n₂ → (m₁ : ℕ) (h₂ : m₁ > n₂) → n₂ ≥ gcd/cost (m₁ , n₂ , h₂)) n →
                    ∀ m → (h : m > n) → n ≥ gcd/cost (m , n , h)) of λ {
                  (zero) → λ ih _ _ → ≤-reflexive refl
                  ; (suc n') → λ ih m h' → subst (λ k → suc n' ≥ k) (P.sym (gcd/cost-unfold-suc {m} {n'} {h'}))
                      ( let g1 = ih (m % suc n') (m%n<n m n') (suc n') (m%n<n m n') in
                      <-transʳ g1 (m%n<n m n'))
                  })
            in
            λ ih m h → g ih m h
           ) n

-- computing the clock is fast since it's just projecting the argument
gcd/fast : cmp (Π gcd/i λ _ → F nat)
gcd/fast i@(x , y , h) = gcd/clocked (toℕ y) i

-- the clock is safe w.r.t specification of gcd
gcd/fast≡gcd/spec : ∀ x y h → ◯ (gcd/fast (x , y , h) ≡ ret {nat} (tonat (gcd/spec (toℕ x , toℕ y , h))))
gcd/fast≡gcd/spec x y h = gcd/clocked≡gcd/spec (toℕ y) x y h (id≥gcd/cost x y h)
