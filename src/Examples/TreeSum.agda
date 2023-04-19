{-# OPTIONS --prop --rewriting #-}

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

add/cost : cmp (Π nat λ _ → Π nat λ _ → cost)
add/cost m n = (1 , 1)

add/is-bounded : ∀ m n → IsBounded nat (add m n) (add/cost m n)
add/is-bounded m n =
  bound/step
    {nat}
    (1 , 1)
    (ret (m + n))
    (bound/ret {nat} (m + n))


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

size : val tree → val nat
size (leaf x)     = 0
size (node t₁ t₂) = suc (size t₁ + size t₂)

depth : val tree → val nat
depth (leaf x)     = 0
depth (node t₁ t₂) = suc (depth t₁ ⊔ depth t₂)

sum/cost : cmp (Π tree λ _ → cost)
sum/cost t = size t , depth t

sum/is-bounded : ∀ t → IsBounded nat (sum t) (sum/cost t)
sum/is-bounded (leaf x)     = bound/ret {nat} x
sum/is-bounded (node t₁ t₂) =
  Eq.subst
    (IsBounded nat (sum (node t₁ t₂)))
    (Eq.cong₂ _,_ (N.+-comm _ 1) (N.+-comm _ 1))
    ( bound/bind/const
        {e = sum t₁ & sum t₂}
        {f = λ (n₁ , n₂) → add n₁ n₂}
        (sum/cost t₁ ⊗ sum/cost t₂)
        (1 , 1)
        ( bound/par
            {e₁ = sum t₁}
            {e₂ = sum t₂}
            {c₁ = sum/cost t₁}
            {c₂ = sum/cost t₂}
            (sum/is-bounded t₁)
            (sum/is-bounded t₂)
        )
        (λ (n₁ , n₂) → add/is-bounded n₁ n₂)
    )
