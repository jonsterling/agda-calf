module Examples.Id where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid
open import Calf.Types.Nat
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

module Easy where
  id : cmp (Π nat λ _ → F nat)
  id n = ret n

  id/correct : ∀ n → ◯ (id n ≡ ret n)
  id/correct n u = refl

  id/bound : cmp (Π nat λ _ → F nat)
  id/bound n = ret n

  id/is-bounded : ∀ n → id n ≲[ F nat ] id/bound n
  id/is-bounded n = ≲-refl

  id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → 0)
  id/asymptotic = f[n]≤g[n]via (≲-mono (λ e → bind (F _) e (λ _ → ret _)) ∘ id/is-bounded)

module Hard where
  id : cmp (Π nat λ _ → F nat)
  id zero = ret 0
  id (suc n) =
    step (F nat) 1 (
      bind (F nat) (id n) λ n' →
        ret (suc n')
    )

  id/bound : cmp (Π nat λ _ → F nat)
  id/bound n = step (F nat) n (ret n)

  id/is-bounded : ∀ n → id n ≲[ F nat ] id/bound n
  id/is-bounded zero    = ≲-refl
  id/is-bounded (suc n) =
    let open ≲-Reasoning (F nat) in
    ≲-mono (step (F nat) 1) $
    begin
      bind (F nat) (id n) (λ n' → ret (suc n'))
    ≤⟨ ≲-mono (λ e → bind (F nat) e (ret ∘ suc)) (id/is-bounded n) ⟩
      bind (F nat) (step (F nat) n (ret n)) (λ n' → ret (suc n'))
    ≡⟨⟩
      step (F nat) n (ret (suc n))
    ∎

  id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → n)
  id/asymptotic = f[n]≤g[n]via (≲-mono (λ e → bind (F _) e _) ∘ id/is-bounded)

easy≡hard : ◯ (Easy.id ≡ Hard.id)
easy≡hard u =
  funext λ n →
    begin
      Easy.id n
    ≡⟨ ≲-ext-≡ u (Easy.id/is-bounded n) ⟩
      Easy.id/bound n
    ≡⟨⟩
      ret n
    ≡˘⟨ step/ext (F nat) (ret n) n u ⟩
      Hard.id/bound n
    ≡˘⟨ ≲-ext-≡ u (Hard.id/is-bounded n) ⟩
      Hard.id n
    ∎
      where open ≡-Reasoning
