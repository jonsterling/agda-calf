{-# OPTIONS --rewriting #-}

module Examples.Amortized.DynamicArray where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Product
open import Calf.Data.Bool
open import Calf.Data.Maybe
open import Calf.Data.Nat as Nat using (ℕ; zero; suc; nat; _+_; _∸_; pred; _*_; _^_; _>_)
import Data.Nat.Properties as Nat
open import Calf.Data.List
open import Data.Nat.PredExp2
import Data.List.Properties as List
open import Calf.Data.Equality as Eq using (_≡_; refl; _≡⁺_; ≡⁺-syntax; _≡⁻_; ≡⁻-syntax; module ≡-Reasoning)
open import Function hiding (_⇔_)
open import Relation.Nullary


postulate
  dynamic-array : tp⁺ → tp⁻
record DynamicArray (A : tp⁺) : Set where
  coinductive
  field
    quit   : cmp (F unit)
    append : cmp (Π A λ _ → dynamic-array A)
    get    : cmp (Π nat λ _ → maybe A ⋉ dynamic-array A)
postulate
  dynamic-array/decode : val (U (dynamic-array A)) ≡ DynamicArray A
  {-# REWRITE dynamic-array/decode #-}

  quit/step   : ∀ {c e} → DynamicArray.quit   (step (dynamic-array A) c e) ≡ step (F unit)                                c (DynamicArray.quit   e)
  append/step : ∀ {c e} → DynamicArray.append (step (dynamic-array A) c e) ≡ step (Π A λ _ → dynamic-array A)             c (DynamicArray.append e)
  get/step    : ∀ {c e} → DynamicArray.get    (step (dynamic-array A) c e) ≡ step (Π nat λ _ → maybe A ⋉ dynamic-array A) c (DynamicArray.get    e)
  {-# REWRITE quit/step append/step get/step #-}

Φ : val nat → val nat → ℂ
Φ n m = 2 ^ n ∸ 2 * m

{-# TERMINATING #-}
-- array n m
-- length of allocated array: (2 ^ n)
-- remaining free spaces: m (≤ 2 ^ (pred n))
array : cmp (Π nat λ _ → Π nat λ _ → dynamic-array unit)
DynamicArray.quit (array n m) = step (F unit) (Φ n m) (ret triv)
DynamicArray.append (array n zero) triv = step (dynamic-array unit) (2 ^ n) (array (suc n) pred[2^ n ])
DynamicArray.append (array n (suc m)) triv = array n m
DynamicArray.get (array n m) i with i Nat.<? 2 ^ n ∸ m
... | no ¬p = nothing , array n m
... | yes p = just triv , array n m

{-# TERMINATING #-}
SPEC/array : cmp (Π nat λ _ → dynamic-array unit)
DynamicArray.quit (SPEC/array n) = ret triv
DynamicArray.append (SPEC/array n) triv = step (dynamic-array unit) 2 (SPEC/array (suc n))
DynamicArray.get (SPEC/array n) i with i Nat.<? n
... | no ¬p = nothing , SPEC/array n
... | yes p = just triv , SPEC/array n

postulate
  _≈⁻_ : (d₁ d₂ : cmp (dynamic-array A)) → tp⁻
record _≈_ {A : tp⁺} (d₁ d₂ : cmp (dynamic-array A)) : Set where
  coinductive
  field
    quit   : cmp $
      DynamicArray.quit d₁ ≡⁻[ F unit ] DynamicArray.quit d₂
    append : cmp $
      Π A λ a → DynamicArray.append d₁ a ≈⁻ DynamicArray.append d₂ a
    get    : cmp $
      Π nat λ i →
        (proj₁ (DynamicArray.get d₁ i) ≡⁺[ maybe A ] proj₁ (DynamicArray.get d₂ i)) ⋉
        (proj₂ (DynamicArray.get d₁ i) ≈⁻ proj₂ (DynamicArray.get d₂ i))
postulate
  ≈⁻/decode : {d₁ d₂ : cmp (dynamic-array A)} → val (U (d₁ ≈⁻ d₂)) ≡ d₁ ≈ d₂
  {-# REWRITE ≈⁻/decode #-}

{-# TERMINATING #-}
≈-cong : (c : ℂ) {x y : DynamicArray A} → x ≈ y → step (dynamic-array A) c x ≈ step (dynamic-array A) c y
_≈_.quit (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.quit h)
_≈_.append (≈-cong c h) a = ≈-cong c (_≈_.append h a)
_≈_.get (≈-cong c h) i = proj₁ (_≈_.get h i) , ≈-cong c (proj₂ (_≈_.get h i))

-- from unreleased agda-stdlib
2^n>0 : ∀ (n : ℕ) → 2 ^ n > 0
2^n>0 zero = Nat.s≤s Nat.z≤n
2^n>0 (suc n) = Nat.≤-trans (2^n>0 n) (Nat.m≤m+n (2 ^ n) ((2 ^ n) + zero))

2^-mono : {m n : ℕ} → m Nat.≤ n → 2 ^ m Nat.≤ 2 ^ n
2^-mono {n = n} Nat.z≤n = 2^n>0 n
2^-mono (Nat.s≤s h) = Nat.*-monoʳ-≤ 2 (2^-mono h)

2^suc[pred[n]] : (n : ℕ) → 2 ^ suc (pred n) ∸ 2 Nat.≤ 2 ^ n
2^suc[pred[n]] zero = Nat.z≤n
2^suc[pred[n]] (suc n) = Nat.m∸n≤m (2 ^ suc n) 2

{-# TERMINATING #-}
array≈SPEC/array : (n m : val nat) → m Nat.≤ pred[2^ pred n ] →
  array n m ≈ step (dynamic-array unit) (2 ^ n ∸ 2 * m) (SPEC/array (2 ^ n ∸ m))
_≈_.quit (array≈SPEC/array n m h) = refl
_≈_.append (array≈SPEC/array n zero h) triv =
  Eq.subst₂
    (λ c x →
      step (dynamic-array unit) (2 ^ n) (array (suc n) (2 ^ n ∸ 1)) ≈
      step (dynamic-array unit) (2 ^ n + c) (SPEC/array x))
    (let open ≡-Reasoning in
    begin
      2 ^ suc n ∸ 2 * pred[2^ n ]
    ≡⟨ Eq.cong (2 ^ suc n ∸_) (Nat.*-distribˡ-∸ 2 (2 ^ n) 1) ⟩
      2 ^ suc n ∸ (2 * 2 ^ n ∸ 2)
    ≡⟨⟩
      2 ^ suc n ∸ (2 ^ suc n ∸ 2)
    ≡⟨ Nat.m∸[m∸n]≡n (Nat.*-monoʳ-≤ 2 (2^n>0 n)) ⟩
      2
    ∎)
    (let open ≡-Reasoning in
    begin
      2 ^ suc n ∸ pred[2^ n ]
    ≡⟨⟩
      2 * 2 ^ n ∸ (2 ^ n ∸ 1)
    ≡⟨⟩
      (2 ^ n + (2 ^ n + 0)) ∸ (2 ^ n ∸ 1)
    ≡⟨ Eq.cong (λ x → (2 ^ n) + x ∸ (2 ^ n ∸ 1)) (Nat.+-identityʳ (2 ^ n)) ⟩
      (2 ^ n + 2 ^ n) ∸ (2 ^ n ∸ 1)
    ≡⟨ Nat.+-∸-assoc (2 ^ n) {n = 2 ^ n} {o = 2 ^ n ∸ 1} (Nat.m∸n≤m (2 ^ n) 1) ⟩
      2 ^ n + (2 ^ n ∸ (2 ^ n ∸ 1))
    ≡⟨ Eq.cong (2 ^ n +_) (Nat.m∸[m∸n]≡n (2^n>0 n)) ⟩
      2 ^ n + 1
    ≡⟨ Nat.+-comm (2 ^ n) 1 ⟩
      suc (2 ^ n)
    ∎)
    (≈-cong (2 ^ n)
      {x = array (suc n) pred[2^ n ]}
      {y = step (dynamic-array unit) (2 ^ suc n ∸ 2 * pred[2^ n ]) (SPEC/array (2 ^ suc n ∸ pred[2^ n ]))}
      (array≈SPEC/array (suc n) pred[2^ n ] Nat.≤-refl))
_≈_.append (array≈SPEC/array n (suc m) h) triv =
  Eq.subst₂
    (λ c x → array n m ≈ step (dynamic-array unit) c (SPEC/array x))
    (let
      lemma : suc (suc (m + (m + zero))) Nat.≤ (2 ^ n)
      lemma =
        let open Nat.≤-Reasoning in
        begin
          suc (suc (m + (m + zero)))
        ≡˘⟨ Eq.cong suc (Nat.+-suc m (m + zero)) ⟩
          suc m + (suc m + zero)
        ≤⟨ Nat.+-mono-≤ h (Nat.+-monoˡ-≤ zero h) ⟩
          pred[2^ pred n ] + (pred[2^ pred n ] + zero)
        ≡⟨ Nat.*-distribˡ-∸ 2 (2 ^ pred n) 1 ⟩
          2 ^ suc (pred n) ∸ 2
        ≤⟨ 2^suc[pred[n]] n ⟩
          2 ^ n
        ∎
    in
    let open ≡-Reasoning in
    begin
      2 ^ n ∸ 2 * m
    ≡˘⟨ Nat.[m+n]∸[m+o]≡n∸o 2 (2 ^ n) (2 * m) ⟩
      (2 + 2 ^ n) ∸ (2 + 2 * m)
    ≡⟨ Nat.+-∸-assoc 2 lemma ⟩
      2 + (2 ^ n ∸ (2 + 2 * m))
    ≡⟨ Nat.+-comm 2 (2 ^ n ∸ (2 + 2 * m)) ⟩
      2 ^ n ∸ (2 + 2 * m) + 2
    ≡˘⟨ Eq.cong (λ x → 2 ^ n ∸ x + 2) (Nat.*-distribˡ-+ 2 1 m) ⟩
      2 ^ n ∸ 2 * suc m + 2
    ∎)
    (let open ≡-Reasoning in
    begin
      2 ^ n ∸ m
    ≡˘⟨ Nat.[m+n]∸[m+o]≡n∸o 1 (2 ^ n) m ⟩
      suc (2 ^ n) ∸ suc m
    ≡⟨
      Nat.+-∸-assoc
        1
        (Nat.≤-trans h (Nat.∸-mono (2^-mono {n = n} Nat.pred[n]≤n) (Nat.z≤n {1})))
    ⟩
      suc (2 ^ n ∸ suc m)
    ∎)
    (array≈SPEC/array n m (Nat.<⇒≤ h))
_≈_.get (array≈SPEC/array n m h) i with i Nat.<? 2 ^ n ∸ m
... | no ¬p = refl , array≈SPEC/array n m h
... | yes p = refl , array≈SPEC/array n m h
