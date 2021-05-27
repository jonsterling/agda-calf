{-# OPTIONS --prop --rewriting #-}

module Sorting where

open import Prelude
open import Metalanguage
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

cost = meta ℕ

module InsertionSort where
  open List hiding (list)
  list = List.list 1 nat

  insert : cmp (Π nat λ _ → Π list λ _ → F list)
  insert x l = list/ind l (λ _ → F list) (ret (cons x nil)) inductive-step
    where
      inductive-step : val nat → val list → cmp (F list) → cmp (F list)
      inductive-step y ys ih with Nat.toℕ y ≤ᵇ Nat.toℕ x
      ... | false = ret (cons x (cons y ys))
      ... | true  = bind (F list) ih λ ys' → ret (cons y ys')

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
