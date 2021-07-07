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

  id/cost : cmp (Π nat λ _ → cost)
  id/cost n = 0

  id≤id/cost : ∀ n → IsBounded nat (id n) (id/cost n)
  id≤id/cost n = bound/ret

  id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → 0)
  id/asymptotic = 0 ≤n⇒f[n]≤ 0 g[n]via λ n _ → id≤id/cost n

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
    ≡⟨ Eq.cong (λ e → bind (F nat) e _) (id/correct n u) ⟩
      ret (suc n)
    ∎
      where open ≡-Reasoning

  id/cost : cmp (Π nat λ _ → cost)
  id/cost zero    = 0
  id/cost (suc n) =
    1 + (
      bind cost (id n) λ n' → id/cost n +
        0
    )

  id/cost/closed : cmp (Π nat λ _ → cost)
  id/cost/closed n = n

  id/cost≤id/cost/closed : ∀ n → ◯ (id/cost n ≤ id/cost/closed n)
  id/cost≤id/cost/closed zero    u = ≤-refl
  id/cost≤id/cost/closed (suc n) u =
    begin
      id/cost (suc n)
    ≡⟨⟩
      1 + (
        bind cost (id n) λ n' → id/cost n +
          0
      )
    ≡⟨ Eq.cong (λ e → 1 + bind cost e λ n' → id/cost n + 0) (id/correct n u) ⟩
      1 + (id/cost n + 0)
    ≡⟨ Eq.cong suc (+-identityʳ _) ⟩
      1 + id/cost n
    ≤⟨ +-monoʳ-≤ 1 (id/cost≤id/cost/closed n u) ⟩
      1 + id/cost/closed n
    ≡⟨⟩
      suc n
    ≡⟨⟩
      id/cost/closed (suc n)
    ∎
      where open ≤-Reasoning

  id≤id/cost : ∀ n → IsBounded nat (id n) (id/cost n)
  id≤id/cost zero    = bound/ret
  id≤id/cost (suc n) =
    bound/step 1 _ (
      bound/bind (id/cost n) _ (id≤id/cost n) λ n →
        bound/ret
    )

  id≤id/cost/closed : ∀ n → IsBounded nat (id n) (id/cost/closed n)
  id≤id/cost/closed n = bound/relax (id/cost≤id/cost/closed n) (id≤id/cost n)

  id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → n)
  id/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ n _ → id≤id/cost/closed n

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
