# Treap

In this file, we implement and verify the [treap](https://en.wikipedia.org/wiki/Treap) data structure.

<!--
```agda
{-# OPTIONS --prop --rewriting #-}
```
-->

First, let's import some stuff:
```agda
module Examples.Sequence.Treap where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid

open import Data.Interval
open import Examples.Decalf.ProbabilisticChoice

open import Calf.Data.Product
open import Calf.Data.Nat using (zero; suc)
open import Calf.Data.List


open import Function using (_$_)

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)
```

Here is the definition of treap:
```agda
data ITreap (A : tp⁺) : val (list A) → Set where
  leaf : ITreap A []
  node : {l₁ l₂ : val (list A)}
    (t₁ : ITreap A l₁) (a : val A) (t₂ : ITreap A l₂)
    → ITreap A (l₁ ++ [ a ] ++ l₂)
itreap : (A : tp⁺) → val (list A) → tp⁺
itreap A l = meta⁺ (ITreap A l)
```

Let's implement some stuff:
```agda
i-join :
  cmp $
    Π (list A) λ l₁ → Π (itreap A l₁) λ _ →
    Π A λ a →
    Π (list A) λ l₂ → Π (itreap A l₂) λ _ →
    F (Σ⁺ (list A) λ l →
      (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (itreap A l))
i-join .[] leaf a .[] leaf = ret ([ a ] , refl , node leaf a leaf)
i-join .[] leaf a l₂ t₂@(node t₂₁ a₂ t₂₂) =
  flip (F _) (1 / suc (length l₂))
    (ret ([ a ] ++ _ , refl , node leaf a t₂))
    (bind (F _) (i-join _ leaf a _ t₂₁) λ (l' , h' , t') →
      ret (l' ++ [ a₂ ] ++ _ , Eq.cong (_++ a₂ ∷ _) h' , node t' a₂ t₂₂))
i-join l₁ (node t₁₁ a₁ t₁₂) a .[] leaf = {!   !}
i-join l₁ (node t₁₁ a₁ t₁₂) a l₂ (node t₂₁ a₂ t₂₂) = {!   !}
```
