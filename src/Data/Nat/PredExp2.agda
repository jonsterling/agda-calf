{-# OPTIONS --prop --without-K --rewriting #-}

module Data.Nat.PredExp2 where

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)

open import Data.Nat.Log2 using (⌈log₂_⌉)

pred[2^_] : ℕ → ℕ
pred[2^ n ] = pred (2 ^ n)

lemma/2^suc : ∀ n → 2 ^ n + 2 ^ n ≡ 2 ^ suc n
lemma/2^suc n =
  begin
    2 ^ n + 2 ^ n
  ≡˘⟨ Eq.cong ((2 ^ n) +_) (*-identityˡ (2 ^ n)) ⟩
    2 ^ n + (2 ^ n + 0)
  ≡⟨⟩
    2 ^ n + (2 ^ n + 0 * (2 ^ n))
  ≡⟨⟩
    2 * (2 ^ n)
  ≡⟨⟩
    2 ^ suc n
  ∎
    where open ≡-Reasoning

private
  lemma/1≤2^n : ∀ n → 1 ≤ 2 ^ n
  lemma/1≤2^n zero    = ≤-refl {1}
  lemma/1≤2^n (suc n) =
    begin
      1
    ≤⟨ s≤s z≤n ⟩
      1 + 1
    ≤⟨ +-mono-≤ (lemma/1≤2^n n) (lemma/1≤2^n n) ⟩
      2 ^ n + 2 ^ n
    ≡⟨ lemma/2^suc n ⟩
      2 ^ suc n
    ∎
      where open ≤-Reasoning

  lemma/2^n≢0 : ∀ n → 2 ^ n ≢ zero
  lemma/2^n≢0 n 2^n≡0 with 2 ^ n | lemma/1≤2^n n
  ... | zero | ()

pred[2^]-mono : pred[2^_] Preserves _≤_ ⟶ _≤_
pred[2^]-mono m≤n = pred-mono (2^-mono m≤n)
  where
    2^-mono : (2 ^_) Preserves _≤_ ⟶ _≤_
    2^-mono {y = y} z≤n = lemma/1≤2^n y
    2^-mono (s≤s m≤n) = *-monoʳ-≤ 2 (2^-mono m≤n)

pred[2^suc[n]] : (n : ℕ) → suc (pred[2^ n ] + pred[2^ n ]) ≡ pred[2^ suc n ]
pred[2^suc[n]] n =
  begin
    suc (pred[2^ n ] + pred[2^ n ])
  ≡⟨⟩
    suc (pred (2 ^ n) + pred (2 ^ n))
  ≡˘⟨ +-suc (pred (2 ^ n)) (pred (2 ^ n)) ⟩
    pred (2 ^ n) + suc (pred (2 ^ n))
  ≡⟨ Eq.cong (pred (2 ^ n) +_) (suc-pred (2 ^ n) {{m^n≢0 2 n}}) ⟩
    pred (2 ^ n) + 2 ^ n
  ≡⟨ lemma/pred-+ (2 ^ n) (2 ^ n) (lemma/2^n≢0 n) ⟩
    pred (2 ^ n + 2 ^ n)
  ≡⟨ Eq.cong pred (lemma/2^suc n) ⟩
    pred (2 ^ suc n)
  ≡⟨⟩
    pred[2^ suc n ]
  ∎
    where
      open ≡-Reasoning

      lemma/pred-+ : ∀ m n → m ≢ zero → pred m + n ≡ pred (m + n)
      lemma/pred-+ zero    n m≢zero = contradiction refl m≢zero
      lemma/pred-+ (suc m) n m≢zero = refl

pred[2^log₂] : (n : ℕ) → pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] ≤ n
pred[2^log₂] n = strong-induction n n ≤-refl
  where
    strong-induction : (n m : ℕ) → m ≤ n → pred[2^ ⌈log₂ suc ⌈ m /2⌉ ⌉ ] ≤ m
    strong-induction n zero    h = z≤n
    strong-induction n (suc zero) h = s≤s z≤n
    strong-induction (suc (suc n)) (suc (suc m)) (s≤s (s≤s h)) =
      begin
        pred[2^ ⌈log₂ suc ⌈ suc (suc m) /2⌉ ⌉ ]
      ≡⟨⟩
        pred[2^ suc ⌈log₂ ⌈ suc ⌈ suc (suc m) /2⌉ /2⌉ ⌉ ]
      ≡˘⟨ pred[2^suc[n]] ⌈log₂ ⌈ suc ⌈ suc (suc m) /2⌉ /2⌉ ⌉ ⟩
        suc (pred[2^ ⌈log₂ ⌈ suc ⌈ suc (suc m) /2⌉ /2⌉ ⌉ ] + pred[2^ ⌈log₂ ⌈ suc ⌈ suc (suc m) /2⌉ /2⌉ ⌉ ])
      ≡⟨⟩
        suc (pred[2^ ⌈log₂ ⌈ suc (suc ⌈ m /2⌉) /2⌉ ⌉ ] + pred[2^ ⌈log₂ ⌈ suc (suc ⌈ m /2⌉) /2⌉ ⌉ ])
      ≡⟨⟩
        suc (pred[2^ ⌈log₂ suc ⌈ ⌈ m /2⌉ /2⌉ ⌉ ] + pred[2^ ⌈log₂ suc ⌈ ⌈ m /2⌉ /2⌉ ⌉ ])
      ≤⟨
        s≤s (
          +-mono-≤
            (strong-induction (suc n) ⌈ m /2⌉ (≤-trans (⌊n/2⌋≤n (suc m)) (s≤s h)))
            (strong-induction (suc n) ⌈ m /2⌉ (≤-trans (⌊n/2⌋≤n (suc m)) (s≤s h)))
        )
      ⟩
        suc (⌈ m /2⌉ + ⌈ m /2⌉)
      ≡⟨⟩
        suc (⌊ suc m /2⌋ + ⌈ m /2⌉)
      ≤⟨ s≤s (+-monoʳ-≤ ⌊ suc m /2⌋ (⌈n/2⌉-mono (n≤1+n m))) ⟩
        suc (⌊ suc m /2⌋ + ⌈ suc m /2⌉)
      ≡⟨ Eq.cong suc (⌊n/2⌋+⌈n/2⌉≡n (suc m)) ⟩
        suc (suc m)
      ∎
        where open ≤-Reasoning
