{-# OPTIONS --rewriting #-}

module Examples.Decalf.Basic where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat
import Data.Nat.Properties as Nat
open import Calf.Data.Equality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Function


double : cmp $ Π nat λ _ → F nat
double zero    = ret zero
double (suc n) =
  step (F nat) 1 $
  bind (F nat) (double n) λ n' →
  ret (suc (suc n'))

double/bound : cmp $ Π nat λ _ → F nat
double/bound n = step (F nat) n (ret (2 * n))

double/has-cost : (n : val nat) → double n ≡ double/bound n
double/has-cost zero    = refl
double/has-cost (suc n) =
  let open ≡-Reasoning in
  begin
    (step (F nat) 1 $
    bind (F nat) (double n) λ n' →
    ret (suc (suc n')))
  ≡⟨
    Eq.cong
      (step (F nat) 1)
      (begin
        (bind (F nat) (double n) λ n' →
        ret (suc (suc n')))
      ≡⟨ Eq.cong (λ e → bind (F nat) e λ n' → ret (suc (suc n'))) (double/has-cost n) ⟩
        (bind (F nat) (step (F nat) n (ret (2 * n))) λ n' →
        ret (suc (suc n')))
      ≡⟨⟩
        step (F nat) n (ret (suc (suc (2 * n))))
      ≡˘⟨ Eq.cong (step (F nat) n ∘ ret ∘ suc) (Nat.+-suc n (n + 0)) ⟩
        step (F nat) n (ret (2 * suc n))
      ∎)
  ⟩
    step (F nat) 1 (step (F nat) n (ret (2 * suc n)))
  ≡⟨⟩
    step (F nat) (suc n) (ret (2 * suc n))
  ∎

double/correct : ◯ ((n : val nat) → double n ≡ ret (2 * n))
double/correct u n = Eq.trans (double/has-cost n) (step/ext (F nat) (ret (2 * n)) n u)
