{-# OPTIONS --prop --rewriting #-}

module Sorting where

open import Prelude
open import Metalanguage
open import Sum
open import Unit
import Nat
open import Nat using (nat)
open import Upper
open import Eq
open import Refinement
open import Relation.Binary.PropositionalEquality as Eq
open import Function
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

open List hiding (list)
list = List.list 1 nat

cost = meta ℕ

module InsertionSort where
  insert : cmp (Π nat λ _ → Π list λ _ → F list)
  insert x l = list/ind l (λ _ → F list) (ret (cons x nil)) inductive-step
    where
      inductive-step : val nat → val list → cmp (F list) → cmp (F list)
      inductive-step y ys ys' with Nat.toℕ y ≤ᵇ Nat.toℕ x
      ... | false = ret (cons x (cons y ys))
      ... | true  = bind (F list) ys' (ret ∘ cons y)

  insert/length : ∀ {A} x l → (k : ℕ → A) → bind (meta A) (insert x l) (k ∘ length) ≡ k (suc (length l))
  insert/length {A} x l = list/ind l (λ _ → meta _) (λ k → refl) inductive-step
    where
      inductive-step : (y : val nat) (ys : val list) →
        (∀ k → bind (meta A) (insert x         ys ) (k ∘ length) ≡ k (suc (length         ys ))) →
        (∀ k → bind (meta A) (insert x (cons y ys)) (k ∘ length) ≡ k (suc (length (cons y ys))))
      inductive-step y ys h k with Nat.toℕ y ≤ᵇ Nat.toℕ x
      ... | false = refl
      ... | true  =
        begin
          bind _ (bind (F list) (insert x ys) (ret ∘ cons y)) (k ∘ length)
        ≡⟨⟩
          bind _ (bind (F list) (insert x ys) (ret ∘ cons y)) (k ∘ length)
        ≡⟨ bind/assoc {B = list} {C = meta A} {e = insert x ys} {f1 = ret ∘ cons y} {f2 = k ∘ length} ⟩
          bind _ (insert x ys) (λ ys' → bind {A = list} (meta A) (ret (cons y ys')) (k ∘ length))
        ≡⟨ Eq.cong (bind {A = list} (meta A) (insert x ys)) (funext λ ys' → sym (bind/ret {A = list} {X = meta A} {v = cons y ys'} {f = k ∘ length})) ⟩
          bind _ (insert x ys) (k ∘ length ∘ cons y)
        ≡⟨ h (k ∘ suc) ⟩
          k (suc (length (cons y ys)))
        ∎
          where open ≡-Reasoning

  insert/cost : cmp (Π nat λ _ → Π list λ _ → cost)
  insert/cost _ = length

  insert≤insert/cost : ∀ x l → ub list (insert x l) (insert/cost x l)
  insert≤insert/cost x l = list/ind l (λ _ → meta _) (ub/ret zero) inductive-step
    where
      inductive-step : (y : val nat) (ys : val list) →
        ub list (insert x         ys ) (length         ys ) →
        ub list (insert x (cons y ys)) (length (cons y ys))
      inductive-step y ys h with Nat.toℕ y ≤ᵇ Nat.toℕ x
      ... | false = ub/intro _ (s≤s z≤n) (ret (eq/intro refl))
      ... | true with ub/bind/const _ zero h (λ _ → ub/ret zero)
      ...   | h-bind rewrite +-identityʳ (length ys) = ub/step/suc _ h-bind

  ex-insert : cmp (F list)
  ex-insert = insert (Nat.tonat 3) (of-list (1 ∷ 2 ∷ 4 ∷ []))

  sort : cmp (Π list λ _ → F list)
  sort l = list/ind l (λ _ → F list) (ret nil) λ x _ ys → bind (F list) ys (insert x)

  sort/length : ∀ {A} l → (k : ℕ → A) → bind (meta A) (sort l) (k ∘ length) ≡ k (length l)
  sort/length {A} l = list/ind l (λ l → meta ((k : ℕ → A) → bind (meta A) (sort l) (k ∘ length) ≡ k (length l))) (λ _ → refl) inductive-step
    where
      inductive-step : (x : val nat) (xs : val list) →
        (∀ k → bind (meta A) (sort         xs ) (k ∘ length) ≡ k (length         xs )) →
        (∀ k → bind (meta A) (sort (cons x xs)) (k ∘ length) ≡ k (length (cons x xs)))
      inductive-step x xs h k =
        begin
          bind (meta A) (sort (cons x xs)) (k ∘ length)
        ≡⟨⟩
          bind (meta A) (bind (F list) (sort xs) (insert x)) (k ∘ length)
        ≡⟨ bind/assoc {B = list} {C = meta A} {e = sort xs} {f1 = insert x} ⟩
          bind (meta A) (sort xs) (λ xs' → bind (meta A) (insert x xs') (k ∘ length))
        ≡⟨ Eq.cong (bind (meta A) (sort xs)) (funext λ xs' → insert/length x xs' k)  ⟩
          bind (meta A) (sort xs) (λ xs' → k (suc (length xs')))
        ≡⟨  h (k ∘ suc)  ⟩
          k (length (cons x xs))
        ∎
          where open ≡-Reasoning

  sort/cost : cmp (Π list λ _ → cost)
  sort/cost l = list/ind l (λ _ → meta ℕ) zero (λ x xs c → suc (insert/cost x xs + c))

  sort≤sort/cost : ∀ l → ub list (sort l) (sort/cost l)
  sort≤sort/cost l = list/ind l (λ _ → meta _) (ub/ret zero) inductive-step
    where
      inductive-step : (x : val nat) (xs : val list) →
        cmp (meta (ub list (sort         xs ) (sort/cost         xs ))) →
        cmp (meta (ub list (sort (cons x xs)) (sort/cost (cons x xs))))
      inductive-step x xs h with ub/step/suc _ (ub/bind (sort/cost xs) (insert/cost x) h (insert≤insert/cost x))
      ... | h-step rewrite sort/length xs (_+_ (sort/cost xs)) | +-comm (sort/cost xs) (length xs) = h-step

  ex-sort : cmp (F list)
  ex-sort = sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))

module MergeSort where
  pair = Σ++ list λ _ → list

  module Option where
    option : tp pos → tp pos
    option A = sum A unit

    some : ∀ {A} → val A → val (option A)
    some = inl

    none : ∀ {A} → val (option A)
    none = inr triv

  open Option

  split : cmp (Π list λ _ → F pair)
  split l =
    bind (F pair) (aux l) (λ { (opt , xs , ys) →
      sum/case _ _ (λ _ → F pair) opt
        (λ x → ret ((cons x xs) , ys))
        (λ _ → ret (xs , ys))
    })
    where
      aux-tp = Σ++ (option nat) λ _ → pair

      aux : cmp (Π list λ _ → F aux-tp)
      aux l =
        list/ind l (λ _ → F aux-tp)
          (ret (none , nil , nil))
          λ x _ acc → bind (F aux-tp) acc (λ { (opt , xs , ys) →
            sum/case _ _ (λ _ → F aux-tp) opt
              (λ y → ret (none , cons x xs , cons y ys))
              (λ _ → ret (some x , xs , ys))
          })

  ex-split : cmp (F pair)
  ex-split = split (of-list (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ []))

  merge/clocked : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → F list)
  merge/clocked zero    (l₁ , l₂) = ret l₁
  merge/clocked (suc k) (l₁ , l₂) =
    list/match l₁ (λ _ → F list)
      (ret l₂)
      λ x xs →
        list/match l₂ (λ _ → F list)
          (ret l₁)
          λ y ys →
            if Nat.toℕ x ≤ᵇ Nat.toℕ y
              then bind (F list) (merge/clocked k (xs , l₂)) (λ res → ret (cons x res))
              else bind (F list) (merge/clocked k (l₁ , xs)) (λ res → ret (cons y res))

  ex-merge : cmp (F list)
  ex-merge = merge/clocked 7 (of-list (2 ∷ 3 ∷ 6 ∷ 8 ∷ []) , of-list (1 ∷ 5 ∷ 8 ∷ []))
