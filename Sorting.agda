{-# OPTIONS --prop --rewriting #-}

module Sorting where

open import Prelude
open import Metalanguage
open import Num
open import Data.Nat
open import Data.Bool using (true ; false)
open import Data.List using ([]; _∷_)

module List where
  postulate
    list : ∀ (n : ℕ) → tp pos → tp pos
    nil : ∀ {A n} → val (list n A)
    cons : ∀ {A n} → val A → val (list n A) → val (list n A)

    list/match : ∀ {A n} → (l : val (list n A)) → (X : val (list n A) → tp neg) → cmp (X nil) →
      ((a : val A) → (l : val (list n A)) → cmp (X (cons a l))) →
      cmp (X l)
    list/match/nil : ∀ {A n X} → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val ((list n A))) →
        cmp (X (cons a l))) →
      list/match nil X e0 e1 ≡ e0
    {-# REWRITE list/match/nil #-}
    list/match/cons : ∀ {A n X} → (a : val A) → (l : val ((list n A))) → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val ((list n A))) →
        cmp (X (cons a l))) →
      list/match (cons a l) X e0 e1 ≡ step' (X (cons a l)) n (e1 a l)
    {-# REWRITE list/match/cons #-}

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

  of-list : ∀ {n} → Data.List.List ℕ → val (list n num)
  of-list []       = nil
  of-list (x ∷ xs) = cons (to-num x) (of-list xs)

module InsertionSort where
  open List hiding (list)
  list = List.list 1 num

  insert : cmp (Π num λ _ → Π list λ _ → F list)
  insert x l = list/ind l (λ _ → F list) (ret (cons x nil)) inductive-step
    where
      inductive-step : val num → val list → val (U (F list)) → cmp (F list)
      inductive-step y ys ih with to-nat y ≤ᵇ to-nat x
      ... | false = ret (cons x (cons y ys))
      ... | true  = bind (F list) ih λ ih → ret (cons y ih)

  ex-insert : cmp (F list)
  ex-insert = insert (to-num 3) (of-list (1 ∷ 2 ∷ 4 ∷ []))

  sort : cmp (Π list λ _ → F list)
  sort l = list/ind l (λ _ → F list) (ret nil) λ x _ ys → bind (F list) ys (insert x)

  ex-sort : cmp (F list)
  ex-sort = sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))
