module Examples.Giralf.Inference where

open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Nat.Properties as Nat
open import Cubical.Relation.Nullary

open import Calf.Value
open import Calf.Value.Nat using (ℕ₌)
open import Calf.Computation.Power
open import Calf.Computation.Product
open import Calf.Giralf.Nat

open <-Reasoning

one≤-of-suc≤ : ∀ {q p : ℕ} → suc q ≤ p → 1 ≤ p
one≤-of-suc≤ h = 1 ≤⟨ suc-≤-suc zero-≤ ⟩ h

one-plus-pred : ∀ {n : ℕ} → 1 ≤ n → 1 + (n ∸ 1) ≡ n
one-plus-pred {n} h =
  1 + (n ∸ 1)       ≡⟨ Nat.+-comm 1 (n ∸ 1) ⟩
  (n ∸ 1) + 1       ≡⟨ ≤-∸-+-cancel h ⟩
  n                 ∎

pred-plus-cancel : ∀ (k : ℕ) {n : ℕ} → 1 ≤ n → ((k + n) ∸ 1) ∸ k ≡ n ∸ 1
pred-plus-cancel k {n} h =
  ((k + n) ∸ 1) ∸ k       ≡⟨ cong (_∸ k) (sym (≤-∸-k h)) ⟩
  (k + (n ∸ 1)) ∸ k       ≡⟨ Nat.∸+ (n ∸ 1) k ⟩
  n ∸ 1                   ∎

pred-plus-left : ∀ {m : ℕ} (n : ℕ) → 1 ≤ m → (m + n) ∸ 1 ≡ (m ∸ 1) + n
pred-plus-left {m} n h =
  (m + n) ∸ 1       ≡⟨ cong (_∸ 1) (Nat.+-comm m n) ⟩
  (n + m) ∸ 1       ≡⟨ sym (≤-∸-k h) ⟩
  n + (m ∸ 1)       ≡⟨ Nat.+-comm n (m ∸ 1) ⟩
  (m ∸ 1) + n       ∎

pred-plus-cancel-left : ∀ {m : ℕ} (n : ℕ) → 1 ≤ m → ((m + n) ∸ 1) ∸ (m ∸ 1) ≡ n
pred-plus-cancel-left {m} n h =
  ((m + n) ∸ 1) ∸ (m ∸ 1)       ≡⟨ cong (_∸ (m ∸ 1)) (pred-plus-left n h) ⟩
  ((m ∸ 1) + n) ∸ (m ∸ 1)       ≡⟨ Nat.∸+ n (m ∸ 1) ⟩
  n                             ∎

split-pred : ∀ {q p : ℕ} → (h : suc q ≤ p) → q + ((p ∸ 1) ∸ q) ≡ p ∸ 1
split-pred {q} {p} h =
  q + ((p ∸ 1) ∸ q)       ≡⟨ Nat.+-comm q ((p ∸ 1) ∸ q) ⟩
  ((p ∸ 1) ∸ q) + q       ≡⟨ ≤-∸-+-cancel (≤-∸-≤ (suc q) p 1 h) ⟩
  p ∸ 1                   ∎

nested-cancel : ∀ {q p : ℕ} (h : suc q ≤ p) →
  ((((p ∸ 1) ∸ q) + (p ∸ 1)) ∸ ((p ∸ 1) ∸ q)) ∸ (((p ∸ 1) ∸ q) + q) ≡ 0
nested-cancel {q} {p} h =
  ((r + s) ∸ r) ∸ (r + q)       ≡⟨ cong (_∸ (r + q)) (Nat.∸+ s r) ⟩
  s ∸ (r + q)                   ≡⟨ cong (s ∸_) (Nat.+-comm r q) ⟩
  s ∸ (q + r)                   ≡⟨ cong (_∸ (q + r)) (sym (split-pred h)) ⟩
  (q + r) ∸ (q + r)             ≡⟨ Nat.n∸n (q + r) ⟩
  0                             ∎
  where
  r = (p ∸ 1) ∸ q
  s = p ∸ 1

arithmetic-0 : ∀ {l1 q2 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ l1
arithmetic-0 h = h

arithmetic-1 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((p5 ∸ 1) ∸ q2) + ((((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)) ≡ ((p5 ∸ 1) ∸ q2) + 0
arithmetic-1 {q2 = q} {p5 = p} _ _ =
  cong (((p ∸ 1) ∸ q) +_) (Nat.∸+ 0 ((p ∸ 1) ∸ q))

arithmetic-2 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 0 ≡ ((((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2))
arithmetic-2 {q2 = q} {p5 = p} _ _ = sym (Nat.∸+ 0 ((p ∸ 1) ∸ q))

arithmetic-3 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 + ((((p5 ∸ 1) ∸ q2) + p5) ∸ 1) ≡ ((p5 ∸ 1) ∸ q2) + p5
arithmetic-3 _ h = one-plus-pred (1 ≤⟨ one≤-of-suc≤ h ⟩ ≤SumRight)

arithmetic-4 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((p5 ∸ 1) ∸ q2) + (((((p5 ∸ 1) ∸ q2) + p5) ∸ 1) ∸ ((p5 ∸ 1) ∸ q2)) ≡ ((((p5 ∸ 1) ∸ q2) + p5) ∸ 1)
arithmetic-4 {q2 = q} {p5 = p} _ h =
  r + (((r + p) ∸ 1) ∸ r)       ≡⟨ cong (r +_) (pred-plus-cancel r (one≤-of-suc≤ h)) ⟩
  r + (p ∸ 1)                   ≡⟨ ≤-∸-k (one≤-of-suc≤ h) ⟩
  (r + p) ∸ 1                   ∎
  where
  r = (p ∸ 1) ∸ q

arithmetic-5 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((((q2 + p5) ∸ 1) ∸ q2) + 0) ≡ (((((p5 ∸ 1) ∸ q2) + p5) ∸ 1) ∸ ((p5 ∸ 1) ∸ q2))
arithmetic-5 {q2 = q} {p5 = p} _ h =
  (((q + p) ∸ 1) ∸ q) + 0       ≡⟨ cong (_+ 0) (pred-plus-cancel q (one≤-of-suc≤ h)) ⟩
  (p ∸ 1) + 0                   ≡⟨ Nat.+-zero (p ∸ 1) ⟩
  p ∸ 1                         ≡⟨ sym (pred-plus-cancel r (one≤-of-suc≤ h)) ⟩
  ((r + p) ∸ 1) ∸ r             ∎
  where
  r = (p ∸ 1) ∸ q

arithmetic-6 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → (((q2 + p5) ∸ 1) ∸ q2) ≡ q2 + ((p5 ∸ 1) ∸ q2)
arithmetic-6 {q2 = q} {p5 = p} _ h =
  ((q + p) ∸ 1) ∸ q       ≡⟨ pred-plus-cancel q (one≤-of-suc≤ h) ⟩
  p ∸ 1                   ≡⟨ sym (split-pred h) ⟩
  q + ((p ∸ 1) ∸ q)       ∎

arithmetic-7 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → q2 ≡ q2
arithmetic-7 _ _ = refl

arithmetic-8 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → suc q2 ≤ q2 + p5
arithmetic-8 _ h = suc _ ≤⟨ h ⟩ ≤SumRight

arithmetic-9-left : ∀ {l1 q2 : ℕ} → 1 ≤ l1 → suc q2 ≤ l1 → 1 ≤ l1
arithmetic-9-left h _ = h

arithmetic-9-right : ∀ {l1 q2 : ℕ} → 1 ≤ l1 → suc q2 ≤ l1 → 1 + q2 ≤ l1
arithmetic-9-right _ h = h

arithmetic-10 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((p5 ∸ 1) ∸ q2) + ((((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)) ≡ ((p5 ∸ 1) ∸ q2) + 0
arithmetic-10 = arithmetic-1

arithmetic-11 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 0 ≡ ((((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2))
arithmetic-11 = arithmetic-2

arithmetic-12 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → zero ≡ zero
arithmetic-12 _ _ = refl

arithmetic-13 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 + (p5 ∸ 1) ≡ p5
arithmetic-13 _ h = one-plus-pred (one≤-of-suc≤ h)

arithmetic-14 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((p5 ∸ 1) ∸ q2) + ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)) ≡ ((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)
arithmetic-14 {q2 = q} {p5 = p} _ _ =
  cong (((p ∸ 1) ∸ q) +_) (Nat.∸+ (p ∸ 1) ((p ∸ 1) ∸ q))

arithmetic-15 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → (q2 + ((p5 ∸ 1) ∸ q2)) + ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2) ∸ (((p5 ∸ 1) ∸ q2) + q2)) ≡ (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)
arithmetic-15 {q2 = q} {p5 = p} _ h =
  (q + r) + (((r + s) ∸ r) ∸ (r + q))       ≡⟨ cong₂ _+_ refl (nested-cancel h) ⟩
  (q + r) + 0                               ≡⟨ Nat.+-zero (q + r) ⟩
  q + r                                     ≡⟨ split-pred h ⟩
  s                                         ≡⟨ sym (Nat.∸+ s r) ⟩
  (r + s) ∸ r                               ∎
  where
  r = (p ∸ 1) ∸ q
  s = p ∸ 1

arithmetic-16 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 0 + 0 ≡ ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2) ∸ (((p5 ∸ 1) ∸ q2) + q2))
arithmetic-16 {q2 = q} {p5 = p} _ h =
  0 + 0                         ≡⟨ sym (nested-cancel h) ⟩
  ((r + s) ∸ r) ∸ (r + q)       ∎
  where
  r = (p ∸ 1) ∸ q
  s = p ∸ 1

arithmetic-17 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → (q2 + p5) ∸ 1 ≡ q2 + (q2 + ((p5 ∸ 1) ∸ q2))
arithmetic-17 {q2 = q} {p5 = p} _ h =
  (q + p) ∸ 1                   ≡⟨ sym (≤-∸-k (one≤-of-suc≤ h)) ⟩
  q + (p ∸ 1)                   ≡⟨ cong (q +_) (sym (split-pred h)) ⟩
  q + (q + ((p ∸ 1) ∸ q))       ∎

arithmetic-18 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → q2 ≡ q2
arithmetic-18 _ _ = refl

arithmetic-19-left : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 ≤ q2 + p5
arithmetic-19-left _ h = 1 ≤⟨ one≤-of-suc≤ h ⟩ ≤SumRight

arithmetic-19-right : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 + q2 ≤ q2 + p5
arithmetic-19-right _ h = suc _ ≤⟨ h ⟩ ≤SumRight

arithmetic-20 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((p5 ∸ 1) ∸ q2) + ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)) ≡ ((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)
arithmetic-20 = arithmetic-14

arithmetic-21 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → ((((q2 + p5) ∸ 1) ∸ q2) + 0) ≡ (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)
arithmetic-21 {q2 = q} {p5 = p} _ h =
  (((q + p) ∸ 1) ∸ q) + 0       ≡⟨ cong (_+ 0) (pred-plus-cancel q (one≤-of-suc≤ h)) ⟩
  (p ∸ 1) + 0                   ≡⟨ Nat.+-zero (p ∸ 1) ⟩
  p ∸ 1                         ≡⟨ sym (Nat.∸+ (p ∸ 1) r) ⟩
  (r + (p ∸ 1)) ∸ r             ∎
  where
  r = (p ∸ 1) ∸ q

arithmetic-22 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → (((q2 + p5) ∸ 1) ∸ q2) ≡ q2 + ((p5 ∸ 1) ∸ q2)
arithmetic-22 = arithmetic-6

arithmetic-23 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → q2 ≡ q2
arithmetic-23 _ _ = refl

arithmetic-24-left : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 ≤ q2 + p5
arithmetic-24-left = arithmetic-19-left

arithmetic-24-right : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 + q2 ≤ q2 + p5
arithmetic-24-right = arithmetic-19-right

arithmetic-25 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → (p5 ∸ 1) + ((0 + (p5 ∸ 1)) ∸ (p5 ∸ 1)) ≡ 0 + (p5 ∸ 1)
arithmetic-25 {p5 = p} _ _ =
  (p ∸ 1) + ((0 + (p ∸ 1)) ∸ (p ∸ 1))       ≡⟨ cong ((p ∸ 1) +_) (Nat.+∸ 0 (p ∸ 1)) ⟩
  (p ∸ 1) + 0                               ≡⟨ Nat.+-zero (p ∸ 1) ⟩
  0 + (p ∸ 1)                               ∎

arithmetic-26 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 0 + 0 ≡ (0 + (p5 ∸ 1)) ∸ (p5 ∸ 1)
arithmetic-26 {p5 = p} _ _ = sym (Nat.+∸ 0 (p ∸ 1))

arithmetic-27 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → (q2 + p5) ∸ 1 ≡ q2 + (p5 ∸ 1)
arithmetic-27 _ h = sym (≤-∸-k (one≤-of-suc≤ h))

arithmetic-28 : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → q2 ≡ q2
arithmetic-28 _ _ = refl

arithmetic-29-left : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 ≤ q2 + p5
arithmetic-29-left = arithmetic-19-left

arithmetic-29-right : ∀ {l1 q2 p5 : ℕ} → suc q2 ≤ l1 → suc q2 ≤ p5 → 1 + q2 ≤ q2 + p5
arithmetic-29-right = arithmetic-19-right

arithmetic-30 : ∀ {q2 : ℕ} → 1 ≤ q2 → 1 ≤ q2
arithmetic-30 h = h

arithmetic-31 : 0 ≡ 0 + 0
arithmetic-31 = refl

arithmetic-32 : ∀ {q2 p17 : ℕ} → 1 ≤ q2 → (((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)) + 0 ≡ p17
arithmetic-32 {q2 = q} {p17 = p} h =
  (((q + p) ∸ 1) ∸ (q ∸ 1)) + 0       ≡⟨ cong (_+ 0) (pred-plus-cancel-left p h) ⟩
  p + 0                               ≡⟨ Nat.+-zero p ⟩
  p                                   ∎

arithmetic-33 : ∀ {q2 p17 : ℕ} → 1 ≤ q2 → ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1) ≡ p17
arithmetic-33 {p17 = p} h = pred-plus-cancel-left p h

arithmetic-34 : ∀ {q2 : ℕ} → 1 ≤ q2 → q2 ∸ 1 ≡ q2 ∸ 1
arithmetic-34 _ = refl

arithmetic-35 : ∀ {q2 p17 : ℕ} → 1 ≤ q2 → 1 + (q2 ∸ 1) ≤ q2 + p17
arithmetic-35 {q2 = q} h =
  1 + (q ∸ 1) ≡≤⟨ one-plus-pred h ⟩
  ≤SumLeft

arithmetic-36-left : ∀ {q2 p17 : ℕ} → 1 ≤ q2 → 1 ≤ q2 + p17
arithmetic-36-left h = 1 ≤⟨ h ⟩ ≤SumLeft

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with ≤Dec m n
... | yes p = true
... | no ¬p = false

snoc : ∀ {l1 q2 : ℕ} → (1 + q2 ≤ l1) → ⟨ X₌ ⟩ → CList₂ (l1) (q2) (X₌) , (((l1 ∸ 1) ∸ q2) + 0) ⊢ CList₂ ((l1 ∸ 1) ∸ q2) (q2) (X₌)
snoc {X} {l1} {q2} cs x1 =
  payᴳ refl $
  powappᴳ {X = 1 + q2 ≤ l1} (arithmetic-0 cs) $
  foldr₂ᴳ (λ p5 → (1 + q2 ≤ p5) ⇀ (◁[ (p5 ∸ 1) ∸ q2 ] (CList₂ ((p5 ∸ 1) ∸ q2) (q2) (X))))
    (λ p5 →
      powlamᴳ {X = 1 + q2 ≤ p5} $ λ cs4 →
      getᴳ ((p5 ∸ 1) ∸ q2) refl $
      cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)} (arithmetic-1 cs4 cs4) (x1) $ nil₂ᴳ (arithmetic-2 cs4 cs4))
    (λ p5 → λ xh3 →
      powlamᴳ {X = 1 + q2 ≤ p5} $ λ cs3 →
      getᴳ ((p5 ∸ 1) ∸ q2) refl $
      spendᴳ {q' = (((p5 ∸ 1) ∸ q2) + p5) ∸ 1} 1 (arithmetic-3 cs3 cs3) $
      cons₂ᴳ {q' = ((((p5 ∸ 1) ∸ q2) + p5) ∸ 1) ∸ ((p5 ∸ 1) ∸ q2)} (arithmetic-4 cs3 cs3) (xh3) $
      substᵐᴳ (arithmetic-5 cs3 cs3) $
      subst2ᴳ (λ l q → CList₂ l q X) (arithmetic-6 cs3 cs3) (arithmetic-7 cs3 cs3) $
      payᴳ refl $
      powappᴳ {X = 1 + q2 ≤ q2 + p5} (arithmetic-8 cs3 cs3) $ idᴳ refl)
    (idᴳ refl)

insert : ∀ {l1 q2 : ℕ} → (1 ≤ l1) × (1 + q2 ≤ l1) → ℕ → CList₂ (l1) (q2) ℕ₌ , (((l1 ∸ 1) ∸ q2) + 0) ⊢ CList₂ ((l1 ∸ 1) ∸ q2) (q2) (ℕ₌)
insert {l1} {q2} cs x1 =
  payᴳ {p = (l1 ∸ 1) ∸ q2} {q' = 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ (l1 ∸ 1) (q2) (ℕ₌))} $
  powappᴳ {X = (1 ≤ l1) × (1 + q2 ≤ l1)}
    (arithmetic-9-left (fst cs) (snd cs) , arithmetic-9-right (fst cs) (snd cs)) $
  foldr₂ᴳ (λ p5 → (1 ≤ p5) × (1 + q2 ≤ p5) ⇀ ((◁[ (p5 ∸ 1) ∸ q2 ] (CList₂ ((p5 ∸ 1) ∸ q2) (q2) (ℕ₌))) ×ᶜ (◁[ 0 ] (CList₂ (p5 ∸ 1) (q2) (ℕ₌)))))
    (λ p5 →
      powlamᴳ {X = (1 ≤ p5) × (1 + q2 ≤ p5)} $ λ cs6 →
      pairᴳ
      (
        getᴳ {q' = ((p5 ∸ 1) ∸ q2) + 0} ((p5 ∸ 1) ∸ q2) refl $
        cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + 0) ∸ ((p5 ∸ 1) ∸ q2)} (arithmetic-10 (snd cs6) (snd cs6)) (x1) $ nil₂ᴳ (arithmetic-11 (snd cs6) (snd cs6))
      )
      (
        getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ (arithmetic-12 (snd cs6) (snd cs6))
      )
    )
    (λ p5 → λ xh3 →
      powlamᴳ {X = (1 ≤ p5) × (1 + q2 ≤ p5)} $ λ cs5 →
      spendᴳ {q' = p5 ∸ 1} 1 (arithmetic-13 (snd cs5) (snd cs5)) $
      pairᴳ
      (
        getᴳ {q' = ((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)} ((p5 ∸ 1) ∸ q2) refl $
        if ((x1) ≤ᵇ (xh3)) then (
          cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)} (arithmetic-14 (snd cs5) (snd cs5)) (x1) $
          cons₂ᴳ {q' = ((((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)) ∸ (((p5 ∸ 1) ∸ q2) + q2)} (arithmetic-15 (snd cs5) (snd cs5)) (xh3) $
          substᵐᴳ (arithmetic-16 (snd cs5) (snd cs5)) $ subst2ᴳ (λ l q → CList₂ l q ℕ₌) (arithmetic-17 (snd cs5) (snd cs5)) (arithmetic-18 (snd cs5) (snd cs5)) $
          payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ ((q2 + p5) ∸ 1) ∸ q2 ] (CList₂ (((q2 + p5) ∸ 1) ∸ q2) (q2) (ℕ₌))} $
          powappᴳ {X = (1 ≤ q2 + p5) × (1 + q2 ≤ q2 + p5)}
            (arithmetic-19-left (snd cs5) (snd cs5) , arithmetic-19-right (snd cs5) (snd cs5)) $ idᴳ refl
        ) else (
          cons₂ᴳ {q' = (((p5 ∸ 1) ∸ q2) + (p5 ∸ 1)) ∸ ((p5 ∸ 1) ∸ q2)} (arithmetic-20 (snd cs5) (snd cs5)) (xh3) $
          substᵐᴳ (arithmetic-21 (snd cs5) (snd cs5)) $ subst2ᴳ (λ l q → CList₂ l q ℕ₌) (arithmetic-22 (snd cs5) (snd cs5)) (arithmetic-23 (snd cs5) (snd cs5)) $
          payᴳ {p = ((q2 + p5) ∸ 1) ∸ q2} {q' = 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ ((q2 + p5) ∸ 1) (q2) (ℕ₌))} $
          powappᴳ {X = (1 ≤ q2 + p5) × (1 + q2 ≤ q2 + p5)}
            (arithmetic-24-left (snd cs5) (snd cs5) , arithmetic-24-right (snd cs5) (snd cs5)) $ idᴳ refl
        )
      )
      (
        getᴳ {q' = 0 + (p5 ∸ 1)} (0) refl $
        cons₂ᴳ {q' = (0 + (p5 ∸ 1)) ∸ (p5 ∸ 1)} (arithmetic-25 (snd cs5) (snd cs5)) (xh3) $
        substᵐᴳ (arithmetic-26 (snd cs5) (snd cs5)) $ subst2ᴳ (λ l q → CList₂ l q ℕ₌) (arithmetic-27 (snd cs5) (snd cs5)) (arithmetic-28 (snd cs5) (snd cs5)) $
        payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ ((q2 + p5) ∸ 1) ∸ q2 ] (CList₂ (((q2 + p5) ∸ 1) ∸ q2) (q2) (ℕ₌))} $
        powappᴳ {X = (1 ≤ q2 + p5) × (1 + q2 ≤ q2 + p5)}
          (arithmetic-29-left (snd cs5) (snd cs5) , arithmetic-29-right (snd cs5) (snd cs5)) $ idᴳ refl
      )
    )
    (idᴳ refl)



reverse : ∀ {l1 q2 : ℕ} → (1 ≤ q2) → CList₂ (l1) (q2) (X₌) , (0 + 0) ⊢ CList₂ (l1) (q2 ∸ 1) (X₌)
reverse {X} {l1} {q2} cs =
  payᴳ {p = 0} {q' = 0} refl $
  powappᴳ {X = 1 ≤ q2} (arithmetic-30 cs) $
  foldr₂ᴳ (λ p17 → (1 ≤ q2) ⇀ (◁[ 0 ] (CList₂ (p17) (q2 ∸ 1) (X))))
    (λ p17 →
      powlamᴳ {X = 1 ≤ q2} $ λ cs10 →
      getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ arithmetic-31
    )
    (λ p17 → λ yh4 →
      powlamᴳ {X = 1 ≤ q2} $ λ cs7 →
      getᴳ {q' = 0 + p17} (0) refl $
      substᵐᴳ (arithmetic-32 cs7) $ subst2ᴳ (λ p28 p27 → CList₂ (p28) (p27) (X)) (arithmetic-33 cs7) (arithmetic-34 cs7) $
      payᴳ {p = ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0 + 0} refl $
      powappᴳ {X = 1 + (q2 ∸ 1) ≤ q2 + p17} (arithmetic-35 cs7) $
      foldr₂ᴳ (λ p20 → (1 + (q2 ∸ 1) ≤ p20) ⇀ (◁[ (p20 ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((p20 ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (X))))
        (λ p20 →
          powlamᴳ {X = 1 + (q2 ∸ 1) ≤ p20} $ λ cs9 →
          getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
          cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} (arithmetic-1 cs9 cs9) (yh4) $ nil₂ᴳ (arithmetic-2 cs9 cs9)
        )
        (λ p20 → λ xh2 →
          powlamᴳ {X = 1 + (q2 ∸ 1) ≤ p20} $ λ cs8 →
          getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
          spendᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20) ∸ 1} 1 (arithmetic-3 cs8 cs8) $
          cons₂ᴳ {q' = ((((p20 ∸ 1) ∸ (q2 ∸ 1)) + p20) ∸ 1) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} (arithmetic-4 cs8 cs8) (xh2) $
          substᵐᴳ (arithmetic-5 cs8 cs8) $ subst2ᴳ (λ p30 p29 → CList₂ (p30) (p29) (X)) (arithmetic-6 cs8 cs8) (arithmetic-7 cs8 cs8) $
          payᴳ {p = (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0} refl $
          powappᴳ {X = 1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20} (arithmetic-8 cs8 cs8) $ idᴳ refl
        )
        (
          payᴳ {p = 0} {q' = 0} refl $
          powappᴳ {X = 1 ≤ q2} (arithmetic-30 cs) $ idᴳ refl)
    )
    (idᴳ refl)


isort : ∀ {l1 q2 : ℕ} → 1 ≤ q2 → CList₂ (l1) (q2) (ℕ₌) , (0 + 0) ⊢ CList₂ (l1) (q2 ∸ 1) (ℕ₌)
isort {l1} {q2} cs =
  payᴳ {p = 0} {q' = 0} refl $
  powappᴳ {X = 1 ≤ q2} (arithmetic-30 cs) $
  foldr₂ᴳ (λ p17 → (1 ≤ q2) ⇀ (◁[ 0 ] (CList₂ (p17) (q2 ∸ 1) (ℕ₌))))
    (λ p17 →
      powlamᴳ {X = 1 ≤ q2} $ λ cs12 →
      getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ arithmetic-31
    )
    (λ p17 → λ yh4 →
      powlamᴳ {X = 1 ≤ q2} $ λ cs9 →
      getᴳ {q' = 0 + p17} (0) refl $
      substᵐᴳ (arithmetic-32 cs9) $ subst2ᴳ (λ p42 p41 → CList₂ (p42) (p41) (ℕ₌)) (arithmetic-33 cs9) (arithmetic-34 cs9) $
      payᴳ {p = ((q2 + p17) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0 + 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ ((q2 + p17) ∸ 1) (q2 ∸ 1) (ℕ₌))} $
      powappᴳ {X = (1 ≤ q2 + p17) × (1 + (q2 ∸ 1) ≤ q2 + p17)} (arithmetic-36-left cs9 , arithmetic-35 cs9) $
      foldr₂ᴳ (λ p20 → ((1 ≤ p20) × (1 + (q2 ∸ 1) ≤ p20)) ⇀ ((◁[ (p20 ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((p20 ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕ₌))) ×ᶜ (◁[ 0 ] (CList₂ (p20 ∸ 1) (q2 ∸ 1) (ℕ₌)))))
        (λ p20 →
          powlamᴳ {X = (1 ≤ p20) × (1 + (q2 ∸ 1) ≤ p20)} $ λ cs11 →
          pairᴳ (
            getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
            cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + 0) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} (arithmetic-10 (snd cs11) (snd cs11)) (yh4) $ nil₂ᴳ (arithmetic-11 (snd cs11) (snd cs11))
          ) (
            getᴳ {q' = 0 + 0} (0) refl $ nil₂ᴳ arithmetic-31
          )
        )
        (λ p20 → λ xh2 →
          powlamᴳ {X = (1 ≤ p20) × (1 + (q2 ∸ 1) ≤ p20)} $ λ cs10 →
          spendᴳ {q' = p20 ∸ 1} 1 (arithmetic-13 (snd cs10) (snd cs10)) $
          pairᴳ (
            getᴳ {q' = ((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)} ((p20 ∸ 1) ∸ (q2 ∸ 1)) refl $
            if ((yh4) ≤ᵇ (xh2)) then (
              cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} (arithmetic-14 (snd cs10) (snd cs10)) (yh4) $
              cons₂ᴳ {q' = ((((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))) ∸ (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (q2 ∸ 1))} (arithmetic-15 (snd cs10) (snd cs10)) (xh2) $
              substᵐᴳ (arithmetic-16 (snd cs10) (snd cs10)) $ subst2ᴳ (λ p48 p47 → CList₂ (p48) (p47) (ℕ₌)) (arithmetic-17 (snd cs10) (snd cs10)) (arithmetic-18 (snd cs10) (snd cs10)) $
              payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕ₌))} $
              powappᴳ {X = (1 ≤ (q2 ∸ 1) + p20) × (1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20)} (arithmetic-19-left (snd cs10) (snd cs10) , arithmetic-19-right (snd cs10) (snd cs10)) $ idᴳ refl
            ) else (
              cons₂ᴳ {q' = (((p20 ∸ 1) ∸ (q2 ∸ 1)) + (p20 ∸ 1)) ∸ ((p20 ∸ 1) ∸ (q2 ∸ 1))} (arithmetic-20 (snd cs10) (snd cs10)) (xh2) $
              substᵐᴳ (arithmetic-21 (snd cs10) (snd cs10)) $ subst2ᴳ (λ p46 p45 → CList₂ (p46) (p45) (ℕ₌)) (arithmetic-22 (snd cs10) (snd cs10)) (arithmetic-23 (snd cs10) (snd cs10)) $
              payᴳ {p = (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)} {q' = 0} refl $ proj₁ᴳ {B = ◁[ 0 ] (CList₂ (((q2 ∸ 1) + p20) ∸ 1) (q2 ∸ 1) (ℕ₌))} $
              powappᴳ {X = (1 ≤ (q2 ∸ 1) + p20) × (1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20)} (arithmetic-24-left (snd cs10) (snd cs10) , arithmetic-24-right (snd cs10) (snd cs10)) $ idᴳ refl
            )
          ) (
            getᴳ {q' = 0 + (p20 ∸ 1)} (0) refl $
            cons₂ᴳ {q' = (0 + (p20 ∸ 1)) ∸ (p20 ∸ 1)} (arithmetic-25 (snd cs10) (snd cs10)) (xh2) $
            substᵐᴳ (arithmetic-26 (snd cs10) (snd cs10)) $ subst2ᴳ (λ p44 p43 → CList₂ (p44) (p43) (ℕ₌)) (arithmetic-27 (snd cs10) (snd cs10)) (arithmetic-28 (snd cs10) (snd cs10)) $
            payᴳ {p = 0} {q' = 0} refl $ proj₂ᴳ {A = ◁[ (((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1) ] (CList₂ ((((q2 ∸ 1) + p20) ∸ 1) ∸ (q2 ∸ 1)) (q2 ∸ 1) (ℕ₌))} $
            powappᴳ {X = (1 ≤ (q2 ∸ 1) + p20) × (1 + (q2 ∸ 1) ≤ (q2 ∸ 1) + p20)} (arithmetic-29-left (snd cs10) (snd cs10) , arithmetic-29-right (snd cs10) (snd cs10)) $ idᴳ refl
          )
        )
        (
          payᴳ {p = 0} {q' = 0} refl $
          powappᴳ {X = 1 ≤ q2} (arithmetic-30 cs) $ idᴳ refl)
    )
    (idᴳ refl)
