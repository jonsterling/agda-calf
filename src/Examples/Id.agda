{-# OPTIONS --prop --rewriting #-}

module Examples.Id where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid
open import Calf.Types.Nat
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

module Easy where
  id : cmp (Π nat λ _ → F nat)
  id n = ret n

  id/correct : ∀ n → ◯ (id n ≡ ret n)
  id/correct n u = refl

  id/cost : cmp (Π nat λ _ → meta ℂ)
  id/cost n = 0

  id/is-bounded : ∀ n → IsBounded nat (id n) (id/cost n)
  id/is-bounded n = bound/ret {nat} n

  id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → 0)
  id/asymptotic = 0 ≤n⇒f[n]≤ 0 g[n]via λ n _ → id/is-bounded n

module Hard where
  id : cmp (Π nat λ _ → F nat)
  id zero = ret 0
  id (suc n) =
    step (F nat) 1 (
      bind (F nat) (id n) λ n' →
        ret (suc n')
    )

  id/correct : ∀ n → ◯ (id n ≡ ret n)
  id/correct zero    u = refl
  id/correct (suc n) u =
    begin
      id (suc n)
    ≡⟨⟩
      step (F nat) 1 (
        bind (F nat) (id n) λ n' →
          ret (suc n')
      )
    ≡⟨ step/ext (F nat) _ 1 u ⟩
      (bind (F nat) (id n) λ n' →
        ret (suc n'))
    ≡⟨ Eq.cong (λ e → bind (F nat) e λ n' → ret (suc n')) (id/correct n u) ⟩
      ret (suc n)
    ∎
      where open ≡-Reasoning

  id/cost : cmp (Π nat λ _ → meta ℂ)
  id/cost n = n

  id/is-bounded : ∀ n → IsBounded nat (id n) (id/cost n)
  id/is-bounded zero = bound/ret {nat} 0
  id/is-bounded (suc n) =
    bound/step
      1
      (bind (F nat) (id n) λ n' → ret (suc n'))
      (id/is-bounded n)

  id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → n)
  id/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ n _ → id/is-bounded n

easy≡hard : ◯ (Easy.id ≡ Hard.id)
easy≡hard u =
  funext λ n →
    begin
      Easy.id n
    ≡⟨ Easy.id/correct n u ⟩
      ret n
    ≡˘⟨ Hard.id/correct n u ⟩
      Hard.id n
    ∎
      where open ≡-Reasoning
