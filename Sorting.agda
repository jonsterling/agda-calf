{-# OPTIONS --prop --rewriting #-}

module Sorting where

open import Prelude
open import Metalanguage
import Nat
open import Nat using (nat)
open import Upper
open import Eq
open import Refinement
import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (true; false; if_then_else_)
open import Data.List using ([]; _∷_)

module List where
  postulate
    list : ∀ (n : ℕ) → tp pos → tp pos
    nil : ∀ {A n} → val (list n A)
    cons : ∀ {A n} → val A → val (list n A) → val (list n A)

    list/ind : ∀ {A n} → (l : val (list n A)) → (X : val (list n A) → tp neg) → cmp (X nil) →
      ((a : val A) → (l : val (list n A)) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      cmp (X l)
    list/ind/nil : ∀ {A n X} → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val ((list n A))) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      list/ind nil X e0 e1 ≡ e0
    {-# REWRITE list/ind/nil #-}
    list/ind/cons : ∀ {A n X} → (a : val A) → (l : val ((list n A))) → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val ((list n A))) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      list/ind (cons a l) X e0 e1 ≡ step' (X (cons a l)) n (e1 a l (list/ind l X e0 e1))
    {-# REWRITE list/ind/cons #-}

  list/match : ∀ {A n} → (l : val (list n A)) → (X : val (list n A) → tp neg) → cmp (X nil) →
    ((a : val A) → (l : val (list n A)) → cmp (X (cons a l))) →
    cmp (X l)
  list/match l X e0 e1 = list/ind l X e0 (λ a l _ → e1 a l)

  of-list : ∀ {n} → Data.List.List ℕ → val (list n Nat.nat)
  of-list []       = nil
  of-list (x ∷ xs) = cons (Nat.tonat x) (of-list xs)

  length : ∀ {A n} → val (list n A) → cmp (meta ℕ)
  length l = list/ind l (λ _ → meta ℕ) zero λ _ _ → suc

cost = meta ℕ

module InsertionSort where
  open List hiding (list)
  list = List.list 1 nat

  insert : cmp (Π nat λ _ → Π list λ _ → F list)
  insert x l = list/ind l (λ _ → F list) (ret (cons x nil)) inductive-step
    where
      inductive-step : val nat → val list → val (U (F list)) → cmp (F list)
      inductive-step y ys ih with Nat.toℕ y ≤ᵇ Nat.toℕ x
      ... | false = ret (cons x (cons y ys))
      ... | true  = bind (F list) ih λ ih → ret (cons y ih)

  insert/cost : cmp (Π nat λ _ → Π list λ _ → cost)
  insert/cost _ = length

  insert≤insert/cost : ∀ x l → ub list (insert x l) (insert/cost x l)
  insert≤insert/cost x l =
    list/ind
      l
      (λ l → meta (ub list (insert x l) (insert/cost x l)))
      (ub/ret 0)
      inductive-step
    where
      inductive-step : (y : val nat) (ys : val list) → ub list (insert x ys) (length ys) → cmp (meta (ub list (insert x (cons y ys)) (length (cons y ys))))
      inductive-step y ys h with Nat.toℕ y ≤ᵇ Nat.toℕ x
      ... | false = ub/intro _ (s≤s z≤n) (ret (eq/intro refl))
      ... | true  with ub/bind/const _ 0 h (λ _ → ub/ret 0) 
      ...   | h-bind rewrite +-identityʳ (length ys) = ub/step/suc (length ys) h-bind

  ex-insert : cmp (F list)
  ex-insert = insert (Nat.tonat 3) (of-list (1 ∷ 2 ∷ 4 ∷ []))

  sort : cmp (Π list λ _ → F list)
  sort l = list/ind l (λ _ → F list) (ret nil) λ x _ ys → bind (F list) ys (insert x)

  ex-sort : cmp (F list)
  ex-sort = sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))
