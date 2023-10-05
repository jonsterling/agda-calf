{-# OPTIONS --rewriting #-}

module Examples.Exp2 where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Parallel parCostMonoid
open import Calf.Data.Bool
open import Calf.Data.Nat
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; pred; _*_; _^_; _⊔_)
import Data.Nat.Properties as N
open import Data.Nat.PredExp2
open import Data.Empty

open import Function using (_∘_)


Correct : cmp (Π nat λ _ → F nat) → Set
Correct exp₂ = (n : ℕ) → ◯ (exp₂ n ≡ ret (2 ^ n))

module Slow where
  exp₂ : cmp (Π nat λ _ → F nat)
  exp₂ zero = ret (suc zero)
  exp₂ (suc n) =
    bind (F nat) (exp₂ n ∥ exp₂ n) λ (r₁ , r₂) →
      step (F nat) (1 , 1) (ret (r₁ + r₂))

  exp₂/bound : cmp (Π nat λ _ → F nat)
  exp₂/bound n = step (F nat) (pred[2^ n ] , n) (ret (2 ^ n))

  exp₂/is-bounded : ∀ n → exp₂ n ≤⁻[ F nat ] exp₂/bound n
  exp₂/is-bounded zero    = ≤⁻-refl
  exp₂/is-bounded (suc n) =
    let open ≤⁻-Reasoning (F nat) in
    begin
      (bind (F nat) (exp₂ n ∥ exp₂ n) λ (r₁ , r₂) →
        step (F nat) (1 , 1) (ret (r₁ + r₂)))
    ≤⟨
      ≤⁻-mono₂ (λ e₁ e₂ → bind (F nat) (e₁ ∥ e₂) λ (r₁ , r₂) → step (F nat) (1 , 1) (ret (r₁ + r₂)))
        (exp₂/is-bounded n)
        (exp₂/is-bounded n)
    ⟩
      (bind (F nat) ((step (F nat) (pred[2^ n ] , n) (ret (2 ^ n))) ∥ (step (F nat) (pred[2^ n ] , n) (ret (2 ^ n)))) λ (r₁ , r₂) →
        step (F nat) (1 , 1) (ret (r₁ + r₂)))
    ≡⟨⟩
      step (F nat) (pred[2^ n ] + pred[2^ n ] + 1 , n ⊔ n + 1) (ret (2 ^ n + 2 ^ n))
    ≡⟨
      Eq.cong₂ (step (F nat))
        (Eq.cong₂ _,_
          (Eq.trans (N.+-comm _ 1) (pred[2^suc[n]] n))
          (Eq.trans (N.+-comm _ 1) (Eq.cong (1 +_) (N.⊔-idem n))))
        (Eq.cong ret (lemma/2^suc n))
    ⟩
      step (F nat) (pred[2^ suc n ] , suc n) (ret (2 ^ suc n))
    ∎

  exp₂/correct : Correct exp₂
  exp₂/correct n u = Eq.trans (≤⁻-ext-≡ u (exp₂/is-bounded n)) (step/ext (F nat) (ret (2 ^ n)) (pred[2^ n ] , n) u)

  exp₂/asymptotic : given nat measured-via (λ n → n) , exp₂ ∈𝓞(λ n → 2 ^ n , n)
  exp₂/asymptotic =
    f[n]≤g[n]via λ n →
      ≤⁻-mono (λ e → bind (F _) e (λ _ → ret triv))
        (≤⁻-trans (exp₂/is-bounded n) (step-monoˡ-≤⁻ (ret (2 ^ n)) (N.pred[n]≤n {2 ^ n} , N.≤-refl {n})))


module Fast where

  exp₂ : cmp (Π nat λ _ → F nat)
  exp₂ zero = ret (suc zero)
  exp₂ (suc n) =
    bind (F nat) (exp₂ n) λ r →
      step (F nat) (1 , 1) (ret (r + r))

  exp₂/bound : cmp (Π nat λ _ → F nat)
  exp₂/bound n = step (F nat) (n , n) (ret (2 ^ n))

  exp₂/is-bounded : ∀ n → exp₂ n ≤⁻[ F nat ] exp₂/bound n
  exp₂/is-bounded zero    = ≤⁻-refl
  exp₂/is-bounded (suc n) =
    let open ≤⁻-Reasoning (F nat) in
    begin
      (bind (F nat) (exp₂ n) λ r →
        step (F nat) (1 , 1) (ret (r + r)))
    ≤⟨ ≤⁻-mono (λ e → bind (F nat) e λ r → step (F nat) (1 , 1) (ret (r + r))) (exp₂/is-bounded n) ⟩
      (bind (F nat) (step (F nat) (n , n) (ret (2 ^ n))) λ r →
        step (F nat) (1 , 1) (ret (r + r)))
    ≡⟨⟩
      step (F nat) (n + 1 , n + 1) (ret (2 ^ n + 2 ^ n))
    ≡⟨
      Eq.cong₂ (step (F nat))
        (Eq.cong₂ _,_ (N.+-comm _ 1) (N.+-comm _ 1))
        (Eq.cong ret (lemma/2^suc n))
    ⟩
      step (F nat) (suc n , suc n) (ret (2 ^ suc n))
    ∎

  exp₂/correct : Correct exp₂
  exp₂/correct n u = Eq.trans (≤⁻-ext-≡ u (exp₂/is-bounded n)) (step/ext (F nat) (ret (2 ^ n)) (n , n) u)

  exp₂/asymptotic : given nat measured-via (λ n → n) , exp₂ ∈𝓞(λ n → n , n)
  exp₂/asymptotic = f[n]≤g[n]via (≤⁻-mono (λ e → bind (F _) e _) ∘ exp₂/is-bounded)


slow≡fast : ◯ (Slow.exp₂ ≡ Fast.exp₂)
slow≡fast u = funext λ n →
  begin
    Slow.exp₂ n
  ≡⟨ Slow.exp₂/correct n u ⟩
    ret (2 ^ n)
  ≡˘⟨ Fast.exp₂/correct n u ⟩
    Fast.exp₂ n
  ∎
    where open ≡-Reasoning
