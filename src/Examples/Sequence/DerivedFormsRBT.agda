{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.DerivedFormsRBT where

open import Examples.Sequence.RedBlackTree
open import Calf costMonoid

open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Product
open import Data.Product
import Data.Nat.Properties as Nat
import Data.List.Properties as List

open import Level using (0ℓ)
open import Function using (_$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)

variable
  y₁ y₂ : val color
  n₁ n₂ : val nat

record RBT (A : tp pos) (l : val (list A)) : Set where
  constructor ⟪_⟫
  field
    {y} : val color
    {n} : val nat
    t : val (irbt A y n l)
rbt : (A : tp pos) → val (list A) → tp pos
rbt A l = U (meta (RBT A l))

mk : {l l' : val (list A)} → val (rbt A l) → l ≡ l' → val (rbt A l')
mk t h = Eq.subst (λ l → RBT _ l) h t

append : {l₁ l₂ : val (list A)} → cmp $
  Π (irbt A y₁ n₁ l₁) λ _ → Π (irbt A y₂ n₂ l₂) λ _ → F (rbt A (l₁ ++ l₂))
append {A} {l₁ = l₁} {l₂} leaf              t₂ = ret ⟪ t₂ ⟫
append {A} {l₁ = l₁} {l₂} (red   t₁₁ a t₁₂) t₂ =
  step (F (rbt A (l₁ ++ l₂))) 1 $
  bind (F (rbt A (l₁ ++ l₂))) (append t₁₂ t₂) λ { ⟪ t₂' ⟫ →
  bind (F (rbt A (l₁ ++ l₂)))  (i-join _ _ _ t₁₁ a _ _ _ t₂') λ (_ , _ , l , (l≡l₁₁++a++l₂' , t₂)) →
  ret (mk ⟪ t₂ ⟫ (Eq.trans l≡l₁₁++a++l₂' (Eq.sym (List.++-assoc _ ([ a ] ++ _) l₂))))
  }
append {A} {l₁ = l₁} {l₂} (black t₁₁ a t₁₂) t₂ =
  step (F (rbt A (l₁ ++ l₂))) 1 $
  bind (F (rbt A (l₁ ++ l₂))) (append t₁₂ t₂) λ { ⟪ t₂' ⟫ →
  bind (F (rbt A (l₁ ++ l₂)))  (i-join _ _ _ t₁₁ a _ _ _ t₂') λ (_ , _ , l , (l≡l₁₁++a++l₂' , t₂)) →
  ret (mk ⟪ t₂ ⟫ (Eq.trans l≡l₁₁++a++l₂' (Eq.sym (List.++-assoc _ ([ a ] ++ _) l₂))))
  }

append/is-bounded : {!   !}
append/is-bounded = {!   !}


module _ (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) where
  open StrictTotalOrder Key

  𝕂 : tp pos
  𝕂 = U (meta (StrictTotalOrder.Carrier Key))
