{-# OPTIONS --without-K #-}

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
  ≡˘⟨ +-∸-comm (2 ^ n) (m^n>0 2 n) ⟩
    pred (2 ^ n + 2 ^ n)
  ≡⟨ Eq.cong pred (lemma/2^suc n) ⟩
    pred (2 ^ suc n)
  ≡⟨⟩
    pred[2^ suc n ]
  ∎
    where
      open ≡-Reasoning

pred[2^log₂] : (n : ℕ) → pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] ≤ n
pred[2^log₂] n = lemma
  where
    open import Data.Nat.Logarithm.Core
    open import Induction.WellFounded using (Acc; acc)

    lemma : ∀ {n acc} → pred[2^ ⌈log2⌉ (suc ⌈ n /2⌉) acc ] ≤ n
    lemma {zero} = z≤n
    lemma {suc zero} {acc _} = s≤s z≤n
    lemma {suc (suc n)} {acc rs} =
      begin
        pred[2^ ⌈log2⌉ (suc ⌈ suc (suc n) /2⌉) (acc rs) ]
      ≡⟨⟩
        pred[2^ suc (⌈log2⌉ ⌈ suc ⌈ suc (suc n) /2⌉ /2⌉ _) ]
      ≡˘⟨ pred[2^suc[n]] (⌈log2⌉ ⌈ suc ⌈ suc (suc n) /2⌉ /2⌉ _) ⟩
        suc (pred[2^ (⌈log2⌉ ⌈ suc ⌈ suc (suc n) /2⌉ /2⌉ _) ] + pred[2^ (⌈log2⌉ ⌈ suc ⌈ suc (suc n) /2⌉ /2⌉ _) ])
      ≡⟨⟩
        suc (pred[2^ ⌈log2⌉ ⌈ suc (suc ⌈ n /2⌉) /2⌉ _ ] + pred[2^ ⌈log2⌉ ⌈ suc (suc ⌈ n /2⌉) /2⌉ _ ])
      ≡⟨⟩
        suc (pred[2^ ⌈log2⌉ (suc ⌈ ⌈ n /2⌉ /2⌉) _ ] + pred[2^ ⌈log2⌉ (suc ⌈ ⌈ n /2⌉ /2⌉) _ ])
      ≤⟨ s≤s (+-mono-≤ (lemma {⌈ n /2⌉}) (lemma {⌈ n /2⌉})) ⟩
        suc (⌈ n /2⌉ + ⌈ n /2⌉)
      ≡⟨⟩
        suc (⌊ suc n /2⌋ + ⌈ n /2⌉)
      ≤⟨ s≤s (+-monoʳ-≤ ⌊ suc n /2⌋ (⌈n/2⌉-mono (n≤1+n n))) ⟩
        suc (⌊ suc n /2⌋ + ⌈ suc n /2⌉)
      ≡⟨ Eq.cong suc (⌊n/2⌋+⌈n/2⌉≡n (suc n)) ⟩
        suc (suc n)
      ∎
        where open ≤-Reasoning
