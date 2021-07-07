{-# OPTIONS --prop --rewriting #-}

module Examples.TreeSum where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Nat

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_)
open import Data.Nat.Properties as N using ()
open import Data.Product

add : cmp (Π nat λ _ → Π nat λ _ → F nat)
add m n = step (F nat) (1 , 1) (ret (m + n))

add/cost : cmp (Π nat λ _ → Π nat λ _ → cost)
add/cost m n = (1 , 1) ⊕ 𝟘

add/cost/closed : cmp (Π nat λ _ → Π nat λ _ → cost)
add/cost/closed m n = (1 , 1)

add/cost≤add/cost/closed : ∀ m n → ◯ (add/cost m n ≤ add/cost/closed m n)
add/cost≤add/cost/closed m n u = ≤-reflexive (⊕-identityʳ (1 , 1))

add≤add/cost : ∀ m n → IsBounded nat (add m n) (add/cost m n)
add≤add/cost m n = bound/step (1 , 1) _ bound/ret

add≤add/cost/closed : ∀ m n → IsBounded nat (add m n) (add/cost/closed m n)
add≤add/cost/closed m n = bound/relax (add/cost≤add/cost/closed m n) (add≤add/cost m n)


data Tree : Set where
  leaf : val nat → Tree
  node : Tree → Tree → Tree

tree : tp pos
tree = U (meta Tree)

sum : cmp (Π tree λ _ → F nat)
sum (leaf x)     = ret x
sum (node t₁ t₂) =
  bind (F nat) (sum t₁ & sum t₂) λ (n₁ , n₂) →
    add n₁ n₂

sum/total : ∀ t → ◯ (∃ λ n → sum t ≡ ret n)
sum/total (leaf x)     u = x , refl
sum/total (node t₁ t₂) u =
  let (n₁ , ≡₁) = sum/total t₁ u
      (n₂ , ≡₂) = sum/total t₂ u
  in
  n₁ + n₂ , (
    let open ≡-Reasoning in
    begin
      (bind (F nat) (sum t₁ & sum t₂) λ (n₁ , n₂) →
        add n₁ n₂)
    ≡⟨ Eq.cong₂ (λ e₁ e₂ → bind (F nat) (e₁ & e₂) _) ≡₁ ≡₂ ⟩
      add n₁ n₂
    ≡⟨⟩
      step (F nat) (1 , 1) (ret (n₁ + n₂))
    ≡⟨ step/ext (F nat) _ (1 , 1) u ⟩
      ret (n₁ + n₂)
    ∎
  )

sum/cost : cmp (Π tree λ _ → cost)
sum/cost (leaf x)     = 𝟘
sum/cost (node t₁ t₂) =
  bind cost (sum t₁ & sum t₂) λ (n₁ , n₂) → (sum/cost t₁ ⊗ sum/cost t₂) ⊕
    add/cost/closed n₁ n₂

size : val tree → val nat
size (leaf x)     = 0
size (node t₁ t₂) = suc (size t₁ + size t₂)

depth : val tree → val nat
depth (leaf x)     = 0
depth (node t₁ t₂) = suc (depth t₁ ⊔ depth t₂)

sum/cost/closed : cmp (Π tree λ _ → cost)
sum/cost/closed t = size t , depth t

sum/cost≤sum/cost/closed : ∀ t → ◯ (sum/cost t ≤ sum/cost/closed t)
sum/cost≤sum/cost/closed (leaf x)     u = ≤-refl
sum/cost≤sum/cost/closed (node t₁ t₂) u =
  let (_ , ≡₁) = sum/total t₁ u
      (_ , ≡₂) = sum/total t₂ u
  in
  begin
    sum/cost (node t₁ t₂)
  ≡⟨⟩
    (bind cost (sum t₁ & sum t₂) λ (n₁ , n₂) → (sum/cost t₁ ⊗ sum/cost t₂) ⊕
      add/cost/closed n₁ n₂)
  ≡⟨ Eq.cong₂ (λ e₁ e₂ → bind cost (e₁ & e₂) λ (n₁ , n₂) → (sum/cost t₁ ⊗ sum/cost t₂) ⊕ _) ≡₁ ≡₂ ⟩
    sum/cost t₁ ⊗ sum/cost t₂ ⊕ (1 , 1)
  ≤⟨ ⊕-monoˡ-≤ (1 , 1) (⊗-mono-≤ (sum/cost≤sum/cost/closed t₁ u) (sum/cost≤sum/cost/closed t₂ u)) ⟩
    sum/cost/closed t₁ ⊗ sum/cost/closed t₂ ⊕ (1 , 1)
  ≡⟨⟩
    (size t₁ , depth t₁) ⊗ (size t₂ , depth t₂) ⊕ (1 , 1)
  ≡⟨⟩
    size t₁ + size t₂ + 1 , depth t₁ ⊔ depth t₂ + 1
  ≡⟨ Eq.cong₂ _,_ (N.+-comm _ 1) (N.+-comm _ 1) ⟩
    suc (size t₁ + size t₂) , suc (depth t₁ ⊔ depth t₂)
  ≡⟨⟩
    sum/cost/closed (node t₁ t₂)
  ∎
    where open ≤-Reasoning

sum≤sum/cost : ∀ t → IsBounded nat (sum t) (sum/cost t)
sum≤sum/cost (leaf x)     = bound/ret
sum≤sum/cost (node t₁ t₂) =
  bound/bind (sum/cost t₁ ⊗ sum/cost t₂) _ (bound/par (sum≤sum/cost t₁) (sum≤sum/cost t₂)) λ (n₁ , n₂) →
    add≤add/cost/closed n₁ n₂

sum≤sum/cost/closed : ∀ t → IsBounded nat (sum t) (sum/cost/closed t)
sum≤sum/cost/closed t = bound/relax (sum/cost≤sum/cost/closed t) (sum≤sum/cost t)
