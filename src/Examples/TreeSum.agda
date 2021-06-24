{-# OPTIONS --prop --rewriting #-}

module Examples.TreeSum where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Product

nat : tp pos
nat = U (meta ℕ)

add : cmp (Π nat λ _ → Π nat λ _ → F nat)
add m n = step' (F nat) (1 , 1) (ret (m + n))

ub/add : ∀ m n → ub nat (add m n) (1 , 1)
ub/add m n = ub/intro (m + n) ≤-refl (ret (eq/intro refl))

data Tree : Set where
  leaf : val nat → Tree
  node : Tree → Tree → Tree

tree : tp pos
tree = U (meta Tree)

sum : cmp (Π tree λ _ → F nat)
sum (leaf x)     = ret x
sum (node t₁ t₂) =
  bind (F nat) (sum t₁ & sum t₂) λ (v₁ , v₂) → add v₁ v₂

sum/cost : cmp (Π tree λ _ → cost)
sum/cost (leaf x)     = 𝟘
sum/cost (node t₁ t₂) = sum/cost t₁ ⊗ sum/cost t₂ ⊕ (1 , 1)

size : val tree → val nat
size (leaf x)     = 0
size (node t₁ t₂) = suc (size t₁ + size t₂)

depth : val tree → val nat
depth (leaf x)     = 0
depth (node t₁ t₂) = suc (depth t₁ ⊔ depth t₂)

sum/cost/closed : cmp (Π tree λ _ → cost)
sum/cost/closed t = size t , depth t

sum/cost≡sum/cost/closed : ∀ t → sum/cost t ≡ sum/cost/closed t
sum/cost≡sum/cost/closed (leaf x)     = refl
sum/cost≡sum/cost/closed (node t₁ t₂) =
  begin
    sum/cost (node t₁ t₂)
  ≡⟨⟩
    sum/cost t₁ ⊗ sum/cost t₂ ⊕ (1 , 1)
  ≡⟨ Eq.cong (_⊕ (1 , 1)) (Eq.cong₂ _⊗_ (sum/cost≡sum/cost/closed t₁) (sum/cost≡sum/cost/closed t₂)) ⟩
    (size t₁ , depth t₁) ⊗ (size t₂ , depth t₂) ⊕ (1 , 1)
  ≡⟨⟩
    size t₁ + size t₂ + 1 , depth t₁ ⊔ depth t₂ + 1
  ≡⟨ Eq.cong₂ _,_ (N.+-comm _ 1) (N.+-comm _ 1) ⟩
    suc (size t₁ + size t₂) , suc (depth t₁ ⊔ depth t₂)
  ≡⟨⟩
    sum/cost/closed (node t₁ t₂)
  ∎
    where open ≡-Reasoning

sum≤sum/cost : ∀ t → ub (U (meta ℕ)) (sum t) (sum/cost t)
sum≤sum/cost (leaf x)     = ub/ret
sum≤sum/cost (node t₁ t₂) =
  ub/bind/const (sum/cost t₁ ⊗ sum/cost t₂) (1 , 1) (ub/par (sum≤sum/cost t₁) (sum≤sum/cost t₂)) (λ (v₁ , v₂) → ub/add v₁ v₂)
