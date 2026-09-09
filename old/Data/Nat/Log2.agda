{-# OPTIONS --without-K #-}

module Data.Nat.Log2 where

import Data.Nat.Logarithm as Logarithm

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

⌈log₂_⌉ : ℕ → ℕ
⌈log₂_⌉ = Logarithm.⌈log₂_⌉

log₂-mono : ⌈log₂_⌉ Preserves _≤_ ⟶ _≤_
log₂-mono = Logarithm.⌈log₂⌉-mono-≤

⌈log₂n⌉≤n : ∀ n → ⌈log₂ n ⌉ ≤ n
⌈log₂n⌉≤n n =
  let open ≤-Reasoning in
  begin
    ⌈log₂ n ⌉
  ≤⟨ Logarithm.⌈log₂⌉-mono-≤ (n≤2^n n) ⟩
    ⌈log₂ (2 ^ n) ⌉
  ≡⟨ Logarithm.⌈log₂2^n⌉≡n n ⟩
    n
  ∎
  where
    n≤2^n : (n : ℕ) → n ≤ 2 ^ n
    n≤2^n zero = z≤n
    n≤2^n (suc n) =
      let open ≤-Reasoning in
      begin
        1 + n
      ≤⟨ +-mono-≤ (^-monoʳ-≤ 2 (z≤n {n})) (n≤2^n n) ⟩
        2 ^ n + 2 ^ n
      ≡˘⟨ Eq.cong ((2 ^ n) +_) (+-identityʳ (2 ^ n)) ⟩
        2 ^ n + (2 ^ n + 0)
      ≡⟨⟩
        2 * 2 ^ n
      ∎

log₂-suc : ∀ n {k} → ⌈log₂ n ⌉ ≤ suc k → ⌈log₂ ⌈ n /2⌉ ⌉ ≤ k
log₂-suc n {k} h =
  let open ≤-Reasoning in
  begin
    ⌈log₂ ⌈ n /2⌉ ⌉
  ≡⟨ Logarithm.⌈log₂⌈n/2⌉⌉≡⌈log₂n⌉∸1 n ⟩
    pred ⌈log₂ n ⌉
  ≤⟨ ∸-monoˡ-≤ 1 h ⟩
    k
  ∎

⌈log₂n⌉≡0⇒n≤1 : {n : ℕ} → ⌈log₂ n ⌉ ≡ 0 → n ≤ 1
⌈log₂n⌉≡0⇒n≤1 {zero} refl = z≤n
⌈log₂n⌉≡0⇒n≤1 {suc zero} refl = s≤s z≤n
