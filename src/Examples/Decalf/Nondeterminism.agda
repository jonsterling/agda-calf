{-# OPTIONS --rewriting #-}

module Examples.Decalf.Nondeterminism where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat as Nat using (nat; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Nat.Square
open import Calf.Data.List as List using (list; []; _∷_; [_]; _++_; length)
import Data.Fin as Fin
open import Calf.Data.Bool using (bool; false; true; if_then_else_)
open import Calf.Data.Product
open import Calf.Data.Equality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Relation.Nullary
open import Function


postulate
  branch : (X : tp⁻) → cmp X → cmp X → cmp X
  fail : (X : tp⁻) → cmp X

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

  branch/step : (c : ℂ) {e₀ e₁ : cmp X} →
    step X c (branch X e₀ e₁) ≡ branch X (step X c e₀) (step X c e₁)
  fail/step : (c : ℂ) →
    step X c (fail X) ≡ fail X


module QuickSort where
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


module Lookup where
  lookup : cmp $ Π (list A) λ _ → Π nat λ _ → F A
  lookup []       i       = fail (F _)
  lookup (x ∷ xs) zero    = ret x
  lookup (x ∷ xs) (suc i) = step (F _) 1 (lookup xs i)

  lookup/bound : cmp $ Π (list A) λ _ → Π nat λ _ → F A
  lookup/bound l i with i Nat.<? length l
  ... | yes p = step (F _) i (ret (List.lookup l (Fin.fromℕ< p)))
  ... | no _  = fail (F _)

  lookup/is-bounded : (l : val (list A)) (i : val nat) → lookup l i ≤⁻[ F A ] lookup/bound l i
  lookup/is-bounded l i with i Nat.<? length l
  ... | yes p = lemma l i p
    where
      lemma : (l : val (list A)) (i : val nat) (p : i Nat.< length l) → lookup l i ≤⁻[ F A ] step (F _) i (ret (List.lookup l (Fin.fromℕ< p)))
      lemma (x ∷ xs) zero (Nat.s≤s Nat.z≤n) = ≤⁻-refl
      lemma (x ∷ xs) (suc i) (Nat.s≤s p) = ≤⁻-mono (step (F _) 1) (lemma xs i p)
  ... | no ¬p = lemma l i (Nat.≮⇒≥ ¬p)
    where
      lemma : (l : val (list A)) (i : val nat) → i Nat.≥ length l → lookup l i ≤⁻[ F A ] fail (F A)
      lemma []       i       Nat.z≤n     = ≤⁻-refl
      lemma (x ∷ xs) (suc i) (Nat.s≤s p) =
        let open ≤⁻-Reasoning (F _) in
        begin
          step (F _) 1 (lookup xs i)
        ≤⟨ ≤⁻-mono (step (F _) 1) (lemma xs i p) ⟩
          step (F _) 1 (fail (F _))
        ≡⟨ fail/step 1 ⟩
          fail (F _)
        ∎
