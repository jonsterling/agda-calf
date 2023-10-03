module Examples.TreeSum where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Nat
open import Calf.Types.Bounded costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat using (_+_; _⊔_)
open import Data.Nat.Properties as N using ()
open import Data.Product

add : cmp (Π nat λ _ → Π nat λ _ → F nat)
add m n = step (F nat) (1 , 1) (ret (m + n))


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

sum/spec : val tree → val nat
sum/spec (leaf x)     = x
sum/spec (node t₁ t₂) = sum/spec t₁ + sum/spec t₂

size : val tree → val nat
size (leaf x)     = 0
size (node t₁ t₂) = suc (size t₁ + size t₂)

depth : val tree → val nat
depth (leaf x)     = 0
depth (node t₁ t₂) = suc (depth t₁ ⊔ depth t₂)

sum/bound : cmp (Π tree λ _ → F nat)
sum/bound t = step (F nat) (size t , depth t) (ret (sum/spec t))

module _ where
  open import Algebra.Definitions (_≡_ {A = ℂ})

  ⊕-comm : Commutative _⊕_
  ⊕-comm (x₁ , x₂) (y₁ , y₂) = Eq.cong₂ _,_ (N.+-comm x₁ y₁) (N.+-comm x₂ y₂)

sum/has-cost : sum ≡ sum/bound
sum/has-cost = funext aux
  where
    aux : (t : val tree) → sum t ≡ sum/bound t
    aux (leaf x)     = refl
    aux (node t₁ t₂) =
      let open ≡-Reasoning in
      begin
        bind (F nat) (sum t₁ & sum t₂) (λ (n₁ , n₂) → add n₁ n₂)
      ≡⟨ Eq.cong₂ (λ e₁ e₂ → bind (F nat) (e₁ & e₂) (λ (n₁ , n₂) → add n₁ n₂)) (aux t₁) (aux t₂) ⟩
        bind (F nat) (sum/bound t₁ & sum/bound t₂) (λ (n₁ , n₂) → add n₁ n₂)
      ≡⟨⟩
        step (F nat)
          (((size t₁ , depth t₁) ⊗ (size t₂ , depth t₂)) ⊕ (1 , 1))
          (ret (sum/spec t₁ + sum/spec t₂))
      ≡⟨ Eq.cong (λ c → step (F nat) c (ret (sum/spec t₁ + sum/spec t₂))) (⊕-comm _ (1 , 1)) ⟩
        sum/bound (node t₁ t₂)
      ∎

sum/is-bounded : sum ≲[ (Π tree λ _ → F nat) ] sum/bound
sum/is-bounded = ≲-reflexive sum/has-cost
