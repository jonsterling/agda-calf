{-# OPTIONS --rewriting #-}

module Examples.Decalf.Nondeterminism where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat as Nat using (nat; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Nat.Square
open import Calf.Data.List using (list; []; _∷_; [_]; _++_; length)
open import Calf.Data.Bool using (bool; if_then_else_)
open import Calf.Data.Product
open import Calf.Data.Equality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Function


postulate
  branch : (X : tp neg) → cmp X → cmp X → cmp X
  fail : (X : tp neg) → cmp X

  branch/idˡ : {e : cmp X} →
    branch X (fail X) e ≡ e
  branch/idʳ : {e : cmp X} →
    branch X e (fail X) ≡ e
  branch/assoc : {e₀ e₁ e₂ : cmp X} →
    branch X (branch X e₀ e₁) e₂ ≡ branch X e₀ (branch X e₁ e₂)
  branch/comm : {e₀ e₁ : cmp X} →
    branch X e₀ e₁ ≡ branch X e₁ e₀
  branch/idem : {e : cmp X} →
    branch X e e ≡ e

  branch/step : {e₀ e₁ : cmp X} →
    step X c (branch X e₀ e₁) ≡ branch X (step X c e₀) (step X c e₁)
  fail/step :
    step X c (fail X) ≡ fail X


_≤?_ : cmp $ Π nat λ _ → Π nat λ _ → F bool
x ≤? y = ret (x Nat.≤ᵇ y)

choose : cmp $ Π (list nat) λ _ → F (nat ×⁺ list nat)
choose []       = fail (F _)
choose (x ∷ xs) =
  branch (F _)
    (bind (F _) (choose xs) λ (pivot , l) → ret (pivot , x ∷ l))
    (ret (x , xs))

partition : cmp $ Π nat λ _ → Π (list nat) λ _ → F (list nat ×⁺ list nat)
partition pivot []       = ret ([] , [])
partition pivot (x ∷ xs) =
  bind (F _) (partition pivot xs) λ (xs₁ , xs₂) →
  bind (F _) (step (F _) 1 (x ≤? pivot)) λ b →
  if b then ret (x ∷ xs₁ , xs₂) else ret (xs₁ , x ∷ xs₂)

{-# TERMINATING #-}
qsort : cmp $ Π (list nat) λ _ → F (list nat)
qsort []       = ret []
qsort (x ∷ xs) =
  bind (F _) (choose (x ∷ xs)) λ (pivot , l) →
  bind (F _) (partition pivot l) λ (l₁ , l₂) →
  bind (F _) (qsort l₁) λ l₁' →
  bind (F _) (qsort l₂) λ l₂' →
  ret (l₁' ++ [ x ] ++ l₂')

-- qsort/bound : cmp $ Π (list nat) λ _ → F (list nat)
-- qsort/bound l = step (F (list nat)) (length l ²) (ret {!   !})

-- qsort/is-bounded : (l : val (list nat)) → qsort l ≤⁻[ F (list nat) ] qsort/bound l
-- qsort/is-bounded []       = {!   !}
-- qsort/is-bounded (x ∷ xs) = {!   !}
