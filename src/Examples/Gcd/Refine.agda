module Examples.Gcd.Refine where

open import Algebra.Cost
import Calf.CostMonoids as CM

open import Calf CM.ℕ-CostMonoid
open import Calf.Data.Nat
open import Calf.Data.IsBounded CM.ℕ-CostMonoid

open import Examples.Gcd.Euclid
open import Examples.Gcd.Clocked as Clocked

open import Data.Nat.DivMod
open import Data.Nat
open import Relation.Binary.PropositionalEquality as P
open import Function
open import Data.Nat.Properties
open import Data.Product
open import Data.Bool using (Bool; false; true)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n

fib⁻¹/helper : ℕ → ℕ → ℕ
fib⁻¹/helper F zero = 0
fib⁻¹/helper F (suc i) with fib (suc i) ≤? F
... | (true because (ofʸ py)) = suc i
... | (false because (ofⁿ pn)) = fib⁻¹/helper F i

fib⁻¹ : ℕ → ℕ
fib⁻¹ F = fib⁻¹/helper F (1 + F)

fib⁻¹-unfold : ∀ F i → ¬ (fib (suc i) ≤ F) →
               fib⁻¹/helper F (suc i) ≡ fib⁻¹/helper F i
fib⁻¹-unfold F i h with fib (suc i) ≤? F
... | (true because (ofʸ py)) = case (h py) of λ {()}
... | (false because (ofⁿ pn)) = refl

fib-base : ∀ n → 1 ≤ fib (1 + n)
fib-base zero = s≤s z≤n
fib-base (suc n') =
  let g = fib-base n' in
  ≤-trans g (m≤m+n _ _)

fib-inc : ∀ n → n < fib (2 + n)
fib-inc zero = s≤s z≤n
fib-inc (suc n') =
  let g = fib-inc n' in
  let g1 = +-mono-≤ g (fib-base n') in
  subst (λ k → k ≤ fib (2 + suc n')) (P.cong suc (P.trans (+-suc n' 0) (P.cong suc (+-identityʳ _)))) g1

fib-fib⁻¹/helper : ∀ F i → fib (suc i) > F → Σ (fib (fib⁻¹/helper F i) ≤ F) λ _ → F < fib (1 + fib⁻¹/helper F i)
fib-fib⁻¹/helper F zero h = z≤n , h
fib-fib⁻¹/helper F (suc i') h with fib (suc i') ≤? F
... | (true because (ofʸ py)) = py , h
... | (false because (ofⁿ pn)) = fib-fib⁻¹/helper F i' (≰⇒> pn)

fib-fib⁻¹ : ∀ F → Σ (fib (fib⁻¹ F) ≤ F) λ _ → F < fib (1 + fib⁻¹ F)
fib-fib⁻¹ F = fib-fib⁻¹/helper F (1 + F) (fib-inc F)

fib-mono-< : fib Preserves _<_ ⟶ _≤_
fib-mono-< {zero} {zero} h = case h of λ {()}
fib-mono-< {zero} {suc y} h = ≤-trans z≤n (fib-base y)
fib-mono-< {1} {1} (s≤s h) = case h of λ {()}
fib-mono-< {1} {suc (suc y)} h = fib-base (suc y)
fib-mono-< {suc (suc x)} {suc (suc y)} (s≤s (s≤s h)) =
  let g = fib-mono-< h in
  let g1 = fib-mono-< (s≤s h) in
  +-mono-≤ g1 g

-- test : ℕ
-- test = gcd/depth (7 , 4 , s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

gcd/fib : ∀ (n : ℕ) (i@(x , y , h) : m>n) →
          gcd/depth i ≥ 1 + n  →
          Σ (x ≥ fib (2 + n)) λ _ → (y ≥ fib (1 + n))
gcd/fib zero (x , y , h) h1 with 1 ≤? y | 1 ≤? x
... | (true because (ofʸ py)) | (true because (ofʸ px)) = px , py
... | (true because _) | (false because (ofⁿ px)) =
  let g = ≰⇒> px in
  let g1 = n<1⇒n≡0 g in
  let g2 = P.subst (λ x → y < x) g1 h in
  case g2 of λ { () }
... | (false because (ofⁿ py)) | _ rewrite (n<1⇒n≡0 (≰⇒> py)) =
  case h1 of λ { () }
gcd/fib (suc n) (x , y , h) h1 with y
... | zero = let g = n≤0⇒n≡0 h1 in case g of λ {()}
... | y@(suc _) rewrite gcd/depth-unfold-suc {h = h} =
  let g : suc (gcd/depth (y , x % y , m%n<n x y)) ≥ 1 + (suc n)
      g = h1 in
  let g1 = +-cancelˡ-≤ 1 _ _ g in
  let (r1 , r2) = gcd/fib n (y , x % y , m%n<n x y) g1 in
  let r1' : fib n + fib (suc n) ≤ y
      r1' = P.subst (λ n → n ≤ y) (+-comm (fib (suc n)) (fib n)) r1 in
  (let e1 = m≡m%n+[m/n]*n x y in
  let e2 = m/n*n≤m x y in
  let e3 : 1 ≤ x / y
      e3 = m≥n⇒m/n>0 (≤-trans (n≤1+n y)  h) in
  let e4 : 1 * y ≤ x / y * y
      e4 = *-monoˡ-≤ y e3 in
  let e5 = P.subst (λ n → n ≤ x / y * y) (*-identityˡ y) e4 in
  P.subst (λ n → x ≥ n) (P.sym (+-assoc (fib (1 + n)) (fib n) (fib (1 + n)))) (
  P.subst (λ x → x ≥ _) (P.sym e1)
    (+-mono-≤ {x = fib (1 + n)} {y = x % y}
    r2 (≤-trans r1' e5))
  )), r1

gcd/depth/bound : ∀ (n : ℕ) (i@(x , y , h) : m>n) →
                x < fib (2 + n) → y < (fib (1 + n)) →
                gcd/depth i < 1 + n
gcd/depth/bound n i h1 h2 = ≰⇒> (contraposition (gcd/fib n i) (λ { (g1 , g2) → (<⇒≱ h1) g1}))

gcd/depth/closed : m>n → ℕ
gcd/depth/closed i@(x , y , h) = 1 + fib⁻¹ x

gcd/depth≤gcd/depth/closed : ∀ (i@(x , y , h) : m>n) → gcd/depth i ≤ gcd/depth/closed i
gcd/depth≤gcd/depth/closed i@(x , y , h) =
  let g : x < fib (1 + fib⁻¹ x)
      g = fib-fib⁻¹ x .proj₂ in
  let g1 : fib (1 + fib⁻¹ x) ≤ fib (2 + fib⁻¹ x)
      g1 = fib-mono-< {1 + fib⁻¹ x} {2 + fib⁻¹ x} (+-monoˡ-< (fib⁻¹ x) (s≤s (s≤s z≤n))) in
  (<⇒≤ (gcd/depth/bound _ i (<-transˡ g g1) (<-trans h g)))

gcd≤gcd/depth/closed : ∀ i → IsBounded nat (gcd i) (gcd/depth/closed i)
gcd≤gcd/depth/closed i = bound/relax (λ _ → gcd/depth≤gcd/depth/closed i) (gcd≤gcd/depth i)
