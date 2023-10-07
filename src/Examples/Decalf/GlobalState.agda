{-# OPTIONS --rewriting #-}

module Examples.Decalf.GlobalState where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat as Nat using (nat; _*_)
open import Calf.Data.Equality as Eq using (_≡_; module ≡-Reasoning)
open import Function


S : tp⁺
S = nat

variable
  s s₁ s₂ : val S

postulate
  get : (X : tp⁻) → (val S → cmp X) → cmp X
  set : (X : tp⁻) → val S → cmp X → cmp X

  get/get : {e : val S → val S → cmp X} →
    (get X λ s₁ → get X λ s₂ → e s₁ s₂) ≡ (get X λ s → e s s)
  get/set : {e : cmp X} →
    (get X λ s → set X s e) ≡ e
  set/get : {e : val S → cmp X} →
    set X s (get X e) ≡ set X s (e s)
  set/set : {e : cmp X} →
    set X s₁ (set X s₂ e) ≡ set X s₂ e

  get/step : (c : ℂ) {e : val S → cmp X} →
    step X c (get X e) ≡ get X λ s → step X c (e s)
  set/step : (c : ℂ) {e : cmp X} →
    step X c (set X s e) ≡ set X s (step X c e)


module StateDependentCost where
  open import Examples.Decalf.Basic

  e : cmp (F nat)
  e =
    get (F nat) λ n →
    bind (F nat) (double n) λ n' →
    set (F nat) n' $
    ret n

  e/bound : cmp (F nat)
  e/bound =
    get (F nat) λ n →
    set (F nat) (2 * n) $
    step (F nat) n $
    ret n

  e/has-cost : e ≡ e/bound
  e/has-cost =
    Eq.cong (get (F nat)) $ funext λ n →
    let open ≡-Reasoning in
    begin
      ( bind (F nat) (double n) λ n' →
        set (F nat) n' $
        ret n
      )
    ≡⟨ Eq.cong (λ e₁ → bind (F nat) e₁ λ n' → set (F nat) n' (ret n)) (double/has-cost n) ⟩
      ( bind (F nat) (step (F nat) n (ret (2 * n))) λ n' →
        set (F nat) n' $
        ret n
      )
    ≡⟨⟩
      ( step (F nat) n $
        set (F nat) (2 * n) $
        ret n
      )
    ≡⟨ set/step n ⟩
      ( set (F nat) (2 * n) $
        step (F nat) n $
        ret n
      )
    ∎
