module Examples.Exp2 where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; pred; _*_; _^_; _⊔_)
import Data.Nat.Properties as N
open import Data.Nat.PredExp2
open import Data.Product
open import Data.Empty

Correct : cmp (Π nat λ _ → F nat) → Set
Correct exp₂ = (n : ℕ) → ◯ (exp₂ n ≡ ret (2 ^ n))

module Slow where
  exp₂ : cmp (Π nat λ _ → F nat)
  exp₂ zero = ret (suc zero)
  exp₂ (suc n) =
    bind (F nat) (exp₂ n & exp₂ n) λ (r₁ , r₂) →
      step (F nat) (1 , 1) (ret (r₁ + r₂))

  exp₂/correct : Correct exp₂
  exp₂/correct zero    u = refl
  exp₂/correct (suc n) u =
    begin
      exp₂ (suc n)
    ≡⟨⟩
      (bind (F nat) (exp₂ n & exp₂ n) λ (r₁ , r₂) →
        step (F nat) (1 , 1) (ret (r₁ + r₂)))
    ≡⟨ Eq.cong (bind (F nat) (exp₂ n & exp₂ n)) (funext (λ (r₁ , r₂) → step/ext (F nat) _ (1 , 1) u)) ⟩
      (bind (F nat) (exp₂ n & exp₂ n) λ (r₁ , r₂) →
        ret (r₁ + r₂))
    ≡⟨ Eq.cong (λ e → bind (F nat) (e & e) _) (exp₂/correct n u) ⟩
      step (F nat) (𝟘 ⊗ 𝟘) (ret (2 ^ n + 2 ^ n))
    ≡⟨⟩
      ret (2 ^ n + 2 ^ n)
    ≡⟨ Eq.cong ret (lemma/2^suc n) ⟩
      ret (2 ^ suc n)
    ∎
      where open ≡-Reasoning

  exp₂/cost : cmp (Π nat λ _ → cost)
  exp₂/cost zero    = 𝟘
  exp₂/cost (suc n) =
    bind cost (exp₂ n & exp₂ n) λ (r₁ , r₂) → (exp₂/cost n ⊗ exp₂/cost n) ⊕
      ((1 , 1) ⊕ 𝟘)

  exp₂/cost/closed : cmp (Π nat λ _ → cost)
  exp₂/cost/closed n = pred[2^ n ] , n

  exp₂/cost≤exp₂/cost/closed : ∀ n → ◯ (exp₂/cost n ≤ exp₂/cost/closed n)
  exp₂/cost≤exp₂/cost/closed zero    u = ≤-refl
  exp₂/cost≤exp₂/cost/closed (suc n) u =
    let ≡ = exp₂/correct n u in
    let open ≤-Reasoning in
    begin
      exp₂/cost (suc n)
    ≡⟨⟩
      (bind cost (exp₂ n & exp₂ n) λ (r₁ , r₂) → (exp₂/cost n ⊗ exp₂/cost n) ⊕
        ((1 , 1) ⊕ 𝟘))
    ≡⟨ Eq.cong₂ (λ e₁ e₂ → bind cost (e₁ & e₂) λ (r₁ , r₂) → (exp₂/cost n ⊗ exp₂/cost n) ⊕ _) (≡) (≡) ⟩
      (exp₂/cost n ⊗ exp₂/cost n) ⊕ ((1 , 1) ⊕ 𝟘)
    ≡⟨ Eq.cong ((exp₂/cost n ⊗ exp₂/cost n) ⊕_) (⊕-identityʳ _) ⟩
      (exp₂/cost n ⊗ exp₂/cost n) ⊕ (1 , 1)
    ≤⟨ ⊕-monoˡ-≤ (1 , 1) (⊗-mono-≤ (exp₂/cost≤exp₂/cost/closed n u) (exp₂/cost≤exp₂/cost/closed n u)) ⟩
      (exp₂/cost/closed n ⊗ exp₂/cost/closed n) ⊕ (1 , 1)
    ≡⟨ Eq.cong₂ _,_ arithmetic/work arithmetic/span ⟩
        exp₂/cost/closed (suc n)
      ∎
      where
        arithmetic/work : proj₁ (exp₂/cost/closed n ⊗ exp₂/cost/closed n ⊕ (1 , 1)) ≡ proj₁ (exp₂/cost/closed (suc n))
        arithmetic/work =
          begin
            proj₁ (exp₂/cost/closed n ⊗ exp₂/cost/closed n ⊕ (1 , 1))
          ≡⟨⟩
            proj₁ (exp₂/cost/closed n) + proj₁ (exp₂/cost/closed n) + 1
          ≡⟨ N.+-comm _ 1 ⟩
            suc (proj₁ (exp₂/cost/closed n) + proj₁ (exp₂/cost/closed n))
          ≡⟨⟩
            suc (pred[2^ n ] + pred[2^ n ])
          ≡⟨ pred[2^suc[n]] n ⟩
            pred[2^ suc n ]
          ≡⟨⟩
            proj₁ (exp₂/cost/closed (suc n))
          ∎
            where open ≡-Reasoning

        arithmetic/span : proj₂ (exp₂/cost/closed n ⊗ exp₂/cost/closed n ⊕ (1 , 1)) ≡ proj₂ (exp₂/cost/closed (suc n))
        arithmetic/span =
          begin
            proj₂ (exp₂/cost/closed n ⊗ exp₂/cost/closed n ⊕ (1 , 1))
          ≡⟨⟩
            proj₂ (exp₂/cost/closed n) ⊔ proj₂ (exp₂/cost/closed n) + 1
          ≡⟨⟩
            n ⊔ n + 1
          ≡⟨ Eq.cong (_+ 1) (N.⊔-idem n) ⟩
            n + 1
          ≡⟨ N.+-comm _ 1 ⟩
            suc n
          ≡⟨⟩
            proj₂ (exp₂/cost/closed (suc n))
          ∎
            where open ≡-Reasoning

  exp₂≤exp₂/cost : ∀ n → IsBounded nat (exp₂ n) (exp₂/cost n)
  exp₂≤exp₂/cost zero    = bound/ret
  exp₂≤exp₂/cost (suc n) =
    bound/bind (exp₂/cost n ⊗ exp₂/cost n) _ (bound/par (exp₂≤exp₂/cost n) (exp₂≤exp₂/cost n)) λ (r₁ , r₂) →
      bound/step (1 , 1) 𝟘 bound/ret

  exp₂≤exp₂/cost/closed : ∀ n → IsBounded nat (exp₂ n) (exp₂/cost/closed n)
  exp₂≤exp₂/cost/closed n = bound/relax (exp₂/cost≤exp₂/cost/closed n) (exp₂≤exp₂/cost n)

  exp₂/asymptotic : given nat measured-via (λ n → n) , exp₂ ∈𝓞(λ n → 2 ^ n , n)
  exp₂/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ n _ → bound/relax (λ u → N.pred[n]≤n , N.≤-refl) (exp₂≤exp₂/cost/closed n)

module Fast where

  exp₂ : cmp (Π nat λ _ → F nat)
  exp₂ zero = ret (suc zero)
  exp₂ (suc n) =
    bind (F nat) (exp₂ n) λ r →
      step (F nat) (1 , 1) (ret (r + r))

  exp₂/correct : Correct exp₂
  exp₂/correct zero    u = refl
  exp₂/correct (suc n) u =
    begin
      exp₂ (suc n)
    ≡⟨⟩
      (bind (F nat) (exp₂ n) λ r →
        step (F nat) (1 , 1) (ret (r + r)))
    ≡⟨ Eq.cong (bind (F nat) (exp₂ n)) (funext (λ r → step/ext (F nat) (ret (r + r)) (1 , 1) u)) ⟩
      (bind (F nat) (exp₂ n) λ r →
        ret (r + r))
    ≡⟨ Eq.cong (λ e → bind (F nat) e λ r → ret (r + r)) (exp₂/correct n u) ⟩
      (bind (F nat) (ret {nat} (2 ^ n)) λ r →
        ret (r + r))
    ≡⟨⟩
      ret (2 ^ n + 2 ^ n)
    ≡⟨ Eq.cong ret (lemma/2^suc n) ⟩
      ret (2 ^ suc n)
    ∎
      where open ≡-Reasoning

  exp₂/cost : cmp (Π nat λ _ → cost)
  exp₂/cost zero    = 𝟘
  exp₂/cost (suc n) =
    bind cost (exp₂ n) λ r → exp₂/cost n ⊕
      ((1 , 1) ⊕ 𝟘)

  exp₂/cost/closed : cmp (Π nat λ _ → cost)
  exp₂/cost/closed n = n , n

  exp₂/cost≤exp₂/cost/closed : ∀ n → ◯ (exp₂/cost n ≤ exp₂/cost/closed n)
  exp₂/cost≤exp₂/cost/closed zero    u = ≤-refl
  exp₂/cost≤exp₂/cost/closed (suc n) u =
    let open ≤-Reasoning in
    begin
      exp₂/cost (suc n)
    ≡⟨⟩
      (bind cost (exp₂ n) λ r → exp₂/cost n ⊕
        ((1 , 1) ⊕ 𝟘))
    ≡⟨ Eq.cong (λ e → bind cost e λ r → exp₂/cost n ⊕ _) (exp₂/correct n u) ⟩
      exp₂/cost n ⊕ ((1 , 1) ⊕ 𝟘)
    ≤⟨ ⊕-monoˡ-≤ ((1 , 1) ⊕ 𝟘) (exp₂/cost≤exp₂/cost/closed n u) ⟩
      exp₂/cost/closed n ⊕ ((1 , 1) ⊕ 𝟘)
    ≡⟨ Eq.cong (exp₂/cost/closed n ⊕_) (⊕-identityʳ _) ⟩
      exp₂/cost/closed n ⊕ (1 , 1)
    ≡⟨ Eq.cong₂ _,_ (N.+-comm _ 1) (N.+-comm _ 1) ⟩
      exp₂/cost/closed (suc n)
    ∎

  exp₂≤exp₂/cost : ∀ n → IsBounded nat (exp₂ n) (exp₂/cost n)
  exp₂≤exp₂/cost zero    = bound/ret
  exp₂≤exp₂/cost (suc n) =
    bound/bind (exp₂/cost n) _ (exp₂≤exp₂/cost n) λ r →
      bound/step (1 , 1) 𝟘 bound/ret

  exp₂≤exp₂/cost/closed : ∀ n → IsBounded nat (exp₂ n) (exp₂/cost/closed n)
  exp₂≤exp₂/cost/closed n = bound/relax (exp₂/cost≤exp₂/cost/closed n) (exp₂≤exp₂/cost n)

  exp₂/asymptotic : given nat measured-via (λ n → n) , exp₂ ∈𝓞(λ n → n , n)
  exp₂/asymptotic = 0 ≤n⇒f[n]≤ 1 g[n]via λ n _ → Eq.subst (IsBounded _ _) (Eq.sym (⊕-identityʳ _)) (exp₂≤exp₂/cost/closed n)

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
