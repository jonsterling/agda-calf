{-# OPTIONS --prop --rewriting #-}

module Examples.Gcd.Spec where

open import Calf.CostMonoid
import Calf.CostMonoids as CM

open import Calf CM.ℕ-CostMonoid
open import Calf.Types.Nat

open import Examples.Gcd.Euclid
open import Examples.Gcd.Clocked

open import Data.Nat.DivMod
open import Data.Nat
open import Relation.Binary.PropositionalEquality as P
open import Data.Nat.Properties
open import Data.Product

gcd/clocked≡spec/zero : ∀ k x h → k ≥ gcd/depth (x , ℕ.zero , h) →
  ◯ (gcd/clocked k (x , ℕ.zero , h) ≡ ret {nat} x)
gcd/clocked≡spec/zero ℕ.zero x h h1 u = refl
gcd/clocked≡spec/zero (suc k) x h h1 u = refl

suc-cancel-≤ : ∀ {m n} → suc m ≤ suc n → m ≤ n
suc-cancel-≤ (s≤s h) = h

gcd/clocked/mono : ∀ k x y h → k ≥ gcd/depth (x , y , h) →
  gcd/clocked k (x , y , h) ≡ gcd/clocked (suc k) (x , y , h)
gcd/clocked/mono ℕ.zero x ℕ.zero h h1 = refl
gcd/clocked/mono (suc k) x ℕ.zero h h1 = refl
gcd/clocked/mono (suc k) x y@(suc _) h h1 =
  begin
    gcd/clocked (suc k) (x , y , h) ≡⟨ refl ⟩
    step (F nat) 1 (gcd/clocked k (y , x % y , m%n<n x y)) ≡⟨
      P.cong (step (F nat) 1)
        (gcd/clocked/mono k (y) (x % y) (m%n<n x y)
          (suc-cancel-≤ (P.subst (λ r → suc k ≥ r) (gcd/depth-unfold-suc {x} {y} {h}) h1))) ⟩
    step (F nat) 1 (gcd/clocked (suc k) (y , x % y , m%n<n x y))
  ∎
  where open ≡-Reasoning

gcd/clocked≡spec/suc : ∀ k x y h → k ≥ gcd/depth (x , suc y , h) →
  ◯ (gcd/clocked k (x , suc y , h) ≡ gcd/clocked k (suc y , x % suc y , m%n<n x (suc y)))
gcd/clocked≡spec/suc (suc k) x y h h1 u =
  begin
  gcd/clocked (suc k) (x , suc y , h) ≡⟨ refl ⟩
  step (F nat) 1 (gcd/clocked k (suc y , x % suc y , m%n<n x (suc y))) ≡⟨ step/ext (F nat) ((gcd/clocked k (suc y , x % suc y , m%n<n x (suc y)))) 1 u ⟩
  gcd/clocked k (suc y , x % suc y , m%n<n x (suc y)) ≡⟨ gcd/clocked/mono k (suc y) (x % suc y) (m%n<n x (suc y))
    (suc-cancel-≤ (P.subst (λ r → suc k ≥ r) (gcd/depth-unfold-suc {h = h}) h1)) ⟩
  gcd/clocked (suc k) (suc y , x % suc y , m%n<n x (suc y))
  ∎
  where open ≡-Reasoning

gcd≡spec/zero : ∀ x h → ◯ (gcd (x , 0 , h) ≡ ret {nat} x)
gcd≡spec/zero x h = gcd/clocked≡spec/zero (gcd/depth (x , 0 , h)) x h ≤-refl

gcd≡spec/suc : ∀ x y h → ◯ (gcd (x , suc y , h) ≡ gcd (suc y , x % suc y , m%n<n x (suc y)))
gcd≡spec/suc x y h u =
  begin
    gcd (x , suc y , h) ≡⟨ gcd/clocked≡spec/suc (gcd/depth (x , suc y , h)) x y h ≤-refl u ⟩
    gcd/clocked (gcd/depth (x , suc y , h)) (suc y , x % suc y , m%n<n x (suc y)) ≡⟨
      cong (λ k → gcd/clocked k (suc y , x % suc y , m%n<n x (suc y)))
      (gcd/depth-unfold-suc {h = h}) ⟩
    gcd/clocked (suc (gcd/depth (suc y , x % suc y , m%n<n x (suc y)))) (suc y , x % suc y , m%n<n x (suc y)) ≡⟨
      sym (gcd/clocked/mono
        (gcd/depth (suc y , x % suc y , m%n<n x (suc y))) (suc y) (x % suc y) (m%n<n x (suc y)) ≤-refl) ⟩
    gcd/clocked (gcd/depth (suc y , x % suc y , m%n<n x (suc y))) (suc y , x % suc y , m%n<n x (suc y))
  ∎
  where open ≡-Reasoning
