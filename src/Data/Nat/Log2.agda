{-# OPTIONS --prop --without-K --rewriting #-}

module Data.Nat.Log2 where

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq

open import Agda.Builtin.Equality.Rewrite

private
  aux : (P : ℕ → Set) → P zero → P (suc zero) → ((n : ℕ) → P ⌈ suc (suc n) /2⌉ → P (suc (suc n))) →
    (n : ℕ) → (m : ℕ) → m ≤ n → P m
  aux P bc₀ bc₁ is n zero h = bc₀
  aux P bc₀ bc₁ is n (suc zero) h = bc₁
  aux P bc₀ bc₁ is (suc (suc n)) (suc (suc m)) (s≤s (s≤s h)) =
    is m (aux P bc₀ bc₁ is (suc n) ⌈ suc (suc m) /2⌉ (s≤s (≤-trans (⌈n/2⌉≤n m) h)))

strong-induction : (P : ℕ → Set) → P zero → P (suc zero) → ((n : ℕ) → P ⌈ suc (suc n) /2⌉ → P (suc (suc n))) → (n : ℕ) → P n
strong-induction P bc₀ bc₁ is n = aux P bc₀ bc₁ is n n ≤-refl

strong-induction/is : ∀ {P bc₀ bc₁ is n} →
  aux P bc₀ bc₁ is (suc n) ⌈ suc (suc n) /2⌉ (s≤s (≤-trans (⌈n/2⌉≤n n) ≤-refl)) ≡
  strong-induction P bc₀ bc₁ is ⌈ suc (suc n) /2⌉
strong-induction/is {P} {bc₀} {bc₁} {is} {n} = aux/unique
  where
    aux/unique : ∀ {m n₁ n₂ h₁ h₂} → aux P bc₀ bc₁ is n₁ m h₁ ≡ aux P bc₀ bc₁ is n₂ m h₂
    aux/unique {zero} = refl
    aux/unique {suc zero} = refl
    aux/unique {suc (suc m)} {h₁ = s≤s (s≤s h₁)} {h₂ = s≤s (s≤s h₂)} = Eq.cong (is m) aux/unique
{-# REWRITE strong-induction/is #-}

⌈log₂_⌉ : ℕ → ℕ
⌈log₂_⌉ = strong-induction (λ _ → ℕ) zero zero (λ _ → suc)

log₂-mono : ⌈log₂_⌉ Preserves _≤_ ⟶ _≤_
log₂-mono {n₁} {n₂} =
  strong-induction (λ n₁ → ∀ n₂ → n₁ ≤ n₂ → ⌈log₂ n₁ ⌉ ≤ ⌈log₂ n₂ ⌉)
    (λ _ _ → z≤n)
    (λ _ _ → z≤n)
    (λ { n₁ ih (suc (suc n₂)) (s≤s (s≤s h)) → s≤s (ih ⌈ suc (suc n₂) /2⌉ (⌈n/2⌉-mono (s≤s (s≤s h))))})
    n₁
    n₂

⌈log₂n⌉≤n : ∀ n → ⌈log₂ n ⌉ ≤ n
⌈log₂n⌉≤n n = strong-induction' n n ≤-refl
  where
    strong-induction' : (n m : ℕ) → m ≤ n → ⌈log₂ m ⌉ ≤ m
    strong-induction' n zero    h = z≤n
    strong-induction' n (suc zero) h = z≤n
    strong-induction' (suc (suc n)) (suc (suc m)) (s≤s (s≤s h)) =
      s≤s (
        let open ≤-Reasoning in
        begin
          ⌈log₂ suc ⌈ m /2⌉ ⌉
        ≤⟨ strong-induction' (suc n) (suc ⌈ m /2⌉) (s≤s (≤-trans (⌈n/2⌉≤n m) h)) ⟩
          suc ⌈ m /2⌉
        ≤⟨ s≤s (⌈n/2⌉≤n m) ⟩
          suc m
        ∎
      )

log₂-suc : ∀ n {k} → ⌈log₂ n ⌉ ≤ suc k → ⌈log₂ ⌈ n /2⌉ ⌉ ≤ k
log₂-suc zero h = z≤n
log₂-suc (suc zero) h = z≤n
log₂-suc (suc (suc n)) (s≤s h) = h

⌈log₂n⌉≡0⇒n≤1 : {n : ℕ} → ⌈log₂ n ⌉ ≡ 0 → n ≤ 1
⌈log₂n⌉≡0⇒n≤1 {zero} refl = z≤n
⌈log₂n⌉≡0⇒n≤1 {suc zero} refl = s≤s z≤n
