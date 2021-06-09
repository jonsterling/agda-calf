{-# OPTIONS --prop --rewriting #-}

module Sorting where

open import Prelude using (funext)
open import Metalanguage
open import Sum
open import Unit
import Nat
open import Nat using (nat)
open import Upper
open import Eq
open import Refinement
open import PhaseDistinction
open import Relation.Nullary
open import Relation.Binary.Definitions
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; refl; module ≡-Reasoning)
open import Data.Product
open import Function
open import Data.Nat hiding (_≤_; _≤ᵇ_)
open import Data.Nat.Properties

private
  variable
    α : Set

module List where
  open import Data.List public using (List; []; _∷_; length; _++_)
  open import Data.List.Properties public

  private
    variable
      A : tp pos

  postulate
    list : tp pos → tp pos
    list/decode : val (list A) ≡ List (val A)
    {-# REWRITE list/decode #-}

  nil : val (list A)
  nil = []

  cons : val A → val (list A) → val (list A)
  cons = _∷_

  of-list : {α : Set} → (α → val A) → Data.List.List α → val (list A)
  of-list {A} f []       = nil {A}
  of-list {A} f (x ∷ xs) = cons {A} (f x) (of-list {A} f xs)

open List

module Bool where
  open import Data.Bool public using (Bool; true; false)

  postulate
    bool : tp pos
    bool/decode : val bool ≡ Bool
    {-# REWRITE bool/decode #-}

open Bool

record Comparable : Set₁ where
  field
    A : tp pos
    _≤_ : val A → val A → Set
    _≤ᵇ_ : val A → val A → cmp (F bool)
    reflects : ∀ {m n b} → ◯ ((m ≤ᵇ n) ≡ ret b → Reflects (m ≤ n) b)
    antisym : Antisymmetric _≡_ _≤_
    h-cost : {x y : val A} → ub bool (x ≤ᵇ y) 1

NatComparable : Comparable
NatComparable = record
  { A = U (meta ℕ)
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ m n → step' (F bool) 1 (ret (m ≤ᵇ n))
  ; reflects = reflects
  ; antisym = ≤-antisym
  ; h-cost = ub/step/suc 0 (ub/ret 0)
  }
  where
    open Data.Nat

    reflects : ∀ {m n b} → ◯ (step' (F bool) 1 (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} h h' rewrite step'/ext (F bool) (ret (m ≤ᵇ n)) 1 h = {! ≤ᵇ-reflects-≤ m n  !}

module Sorting (M : Comparable) where
  open Comparable M

  open import Data.List.Relation.Binary.Permutation.Propositional as Perm public

  data _≤*_ (x : val A) : val (list A) → Set where
    []  : x ≤* []
    _∷_ : ∀ {y ys} → x ≤ y → x ≤* ys → x ≤* (y ∷ ys)

  data Sorted : val (list A) → Set where
    [] : Sorted []
    _∷_ : ∀ {y ys} → y ≤* ys → Sorted ys → Sorted (y ∷ ys)

  SortedOf : val (list A) → val (list A) → Set
  SortedOf l l' = l ↭ l' × Sorted l'

  SortResult : cmp (Π (list A) λ _ → F (list A)) → val (list A) → Set
  SortResult sort l = ∃ λ l' → ◯ (sort l ≡ ret l') × SortedOf l l'

  IsSort : cmp (Π (list A) λ _ → F (list A)) → Set
  IsSort sort = ∀ l → SortResult sort l

cost = meta ℕ

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module InsertionSort (M : Comparable) where
  open Comparable M
  open Sorting M

  insert : cmp (Π A λ _ → Π (list A) λ _ → F (list A))
  insert x []       = ret (x ∷ [])
  insert x (y ∷ ys) =
    bind (F (list A)) (x ≤ᵇ y)
      λ { false → bind (F (list A)) (insert x ys) (ret ∘ _∷_ y)
        ; true  → ret (x ∷ (y ∷ ys)) }

  insert/length : ∀ x l (κ : ℕ → α) → bind (meta α) (insert x l) (κ ∘ length) ≡ κ (suc (length l))
  insert/length x []       κ = refl
  insert/length x (y ∷ ys) κ with h-cost {x} {y}
  ... | ub/intro false _ h-eq rewrite eq/ref h-eq = insert/length x ys (κ ∘ suc)
  ... | ub/intro true  _ h-eq rewrite eq/ref h-eq = refl

  insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost _ = length

  insert≤insert/cost : ∀ x l → ub (list A) (insert x l) (insert/cost x l)
  insert≤insert/cost x []       = ub/ret zero
  insert≤insert/cost x (y ∷ ys) with h-cost {x} {y}
  ... | ub/intro true  q≤1 h-eq rewrite eq/ref h-eq = ub/intro _ (≤-trans q≤1 (s≤s z≤n)) (ret (eq/intro refl))
  ... | ub/intro {q = q} false q≤1 h-eq rewrite eq/ref h-eq =
          ub/relax
            (begin
              length ys + q + 0
            ≡⟨ +-identityʳ _ ⟩
              length ys + q
            ≡⟨ +-comm (length ys) q ⟩
              q + length ys
            ≤⟨ +-monoˡ-≤ _ q≤1 ⟩
              suc (length ys)
            ∎)
            (ub/bind/const _ _ (ub/step (length ys) q (insert≤insert/cost x ys)) λ _ → ub/ret zero)
            where open ≤-Reasoning

  sort : cmp (Π (list A) λ _ → F (list A))
  sort []       = ret []
  sort (x ∷ xs) = bind (F (list A)) (sort xs) (insert x)

  sort/correct : IsSort sort
  sort/correct l = {!   !}

  sort/length : ∀ l (κ : ℕ → α) → bind (meta α) (sort l) (κ ∘ length) ≡ κ (length l)
  sort/length []       κ = refl
  sort/length (x ∷ xs) κ =
    begin
      bind _ (sort (x ∷ xs)) (κ ∘ length)
    ≡⟨⟩
      bind _ (bind (F (list A)) (sort xs) (insert x)) (κ ∘ length)
    ≡⟨⟩
      bind _ (sort xs) (λ xs' → bind (meta _) (insert x xs') (κ ∘ length))
    ≡⟨ Eq.cong (bind _ (sort xs)) (funext λ xs' → insert/length x xs' κ)  ⟩
      bind _ (sort xs) (λ xs' → κ (suc (length xs')))
    ≡⟨ sort/length xs (κ ∘ suc) ⟩
      κ (length (x ∷ xs))
    ∎
      where open ≡-Reasoning

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost []       = zero
  sort/cost (x ∷ xs) = sort/cost xs + insert/cost x xs

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost []       = ub/ret zero
  sort≤sort/cost (x ∷ xs) with ub/bind (sort/cost xs) length (sort≤sort/cost xs) (insert≤insert/cost x)
  ... | h-bind rewrite sort/length xs (_+_ (sort/cost xs)) = h-bind

module Ex/InsertionSort where
  module Sort = InsertionSort NatComparable

  list' = list (U (meta ℕ))

  ex/insert : cmp (F list')
  ex/insert = Sort.insert 3 (1 ∷ 2 ∷ 4 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 15

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 120

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 76

module MergeSort (M : Comparable) where
  open Comparable M
  open Sorting M

  pair = Σ++ (list A) λ _ → (list A)

  split/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → F pair)
  split/clocked zero    l        = ret ([] , l)
  split/clocked (suc k) []       = ret ([] , [])
  split/clocked (suc k) (x ∷ xs) = bind (F pair) (split/clocked k xs) λ (l₁ , l₂) → ret (x ∷ l₁ , l₂)

  split/clocked/length : ∀ k k' l → k + k' ≡ length l → (κ : ℕ → ℕ → α) →
    bind (meta α) (split/clocked k l) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ k k'
  split/clocked/length zero    _  l        refl _ = refl
  split/clocked/length (suc k) k' (x ∷ xs) h    κ = split/clocked/length k k' xs (suc-injective h) (κ ∘ suc)

  split/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  split/clocked/cost _ _ = zero

  split/clocked≤split/clocked/cost : ∀ k l → ub pair (split/clocked k l) (split/clocked/cost k l)
  split/clocked≤split/clocked/cost zero    l        = ub/ret _
  split/clocked≤split/clocked/cost (suc k) []       = ub/ret _
  split/clocked≤split/clocked/cost (suc k) (x ∷ xs) = ub/bind/const zero zero (split/clocked≤split/clocked/cost k xs) λ _ → ub/ret _

  split : cmp (Π (list A) λ _ → F pair)
  split l = split/clocked ⌊ length l /2⌋ l

  split/length : ∀ l (κ : ℕ → ℕ → α) →
    bind (meta α) (split l) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ ⌊ length l /2⌋ ⌈ length l /2⌉
  split/length l = split/clocked/length ⌊ length l /2⌋ ⌈ length l /2⌉ l (⌊n/2⌋+⌈n/2⌉≡n (length l))

  split/cost : cmp (Π (list A) λ _ → cost)
  split/cost l = split/clocked/cost ⌊ length l /2⌋ l

  split≤split/cost : ∀ l → ub pair (split l) (split/cost l)
  split≤split/cost l = split/clocked≤split/clocked/cost ⌊ length l /2⌋ l

  merge/clocked : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → F (list A))
  merge/clocked zero    (l₁     , l₂    ) = ret (l₁ ++ l₂)
  merge/clocked (suc k) ([]     , l₂    ) = ret l₂
  merge/clocked (suc k) (x ∷ xs , []    ) = ret (x ∷ xs)
  merge/clocked (suc k) (x ∷ xs , y ∷ ys) =
    bind (F (list A)) (x ≤ᵇ y)
      λ { false → bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ _∷_ y)
        ; true  → bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ _∷_ x) }

  merge/clocked/length : ∀ k (l₁ l₂ : val (list A)) (κ : ℕ → α) →
    bind (meta α) (merge/clocked k (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  merge/clocked/length zero    l₁       l₂       κ = Eq.cong κ (length-++ l₁)
  merge/clocked/length (suc k) []       l₂       κ = refl
  merge/clocked/length (suc k) (x ∷ xs) []       κ = Eq.cong (κ ∘ suc) (Eq.sym (+-identityʳ (length xs)))
  merge/clocked/length (suc k) (x ∷ xs) (y ∷ ys) κ with h-cost {x} {y}
  ... | ub/intro false _ h-eq rewrite eq/ref h-eq =
    begin
      bind _ (merge/clocked k (x ∷ xs , ys)) (λ l → (κ ∘ length) (y ∷ l))
    ≡⟨⟩
      bind _ (merge/clocked k (x ∷ xs , ys)) (λ l → (κ ∘ suc) (length l))
    ≡⟨ merge/clocked/length k (x ∷ xs) ys (κ ∘ suc) ⟩
      κ (suc (length (x ∷ xs) + length ys))
    ≡⟨ Eq.cong κ (Eq.sym (+-suc (length (x ∷ xs)) (length ys))) ⟩
      κ (length (x ∷ xs) + length (y ∷ ys))
    ∎
      where open ≡-Reasoning
  ... | ub/intro true  _ h-eq rewrite eq/ref h-eq =
    begin
      bind _ (merge/clocked k (xs , y ∷ ys)) (λ l → (κ ∘ length) (x ∷ l))
    ≡⟨⟩
      bind _ (merge/clocked k (xs , y ∷ ys)) (λ l → (κ ∘ suc) (length l))
    ≡⟨ merge/clocked/length k xs (y ∷ ys) (κ ∘ suc) ⟩
      κ (suc (length xs + length (y ∷ ys)))
    ≡⟨⟩
      κ (length (x ∷ xs) + length (y ∷ ys))
    ∎
      where open ≡-Reasoning

  merge/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → cost)
  merge/clocked/cost k _ = k

  merge/clocked≤merge/clocked/cost : ∀ k p → ub (list A) (merge/clocked k p) (merge/clocked/cost k p)
  merge/clocked≤merge/clocked/cost zero    (l₁     , l₂    ) = ub/ret _
  merge/clocked≤merge/clocked/cost (suc k) ([]     , l₂    ) = ub/ret _
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , []    ) = ub/ret _
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , y ∷ ys) =
    ub/bind/const 1 k h-cost 
      λ { false → ub/bind/const' k zero (+-identityʳ k) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret _
        ; true  → ub/bind/const' k zero (+-identityʳ k) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret _ }

  merge : cmp (Π pair λ _ → F (list A))
  merge (l₁ , l₂) = merge/clocked (length l₁ + length l₂) (l₁ , l₂)

  merge/length : ∀ l₁ l₂ (κ : ℕ → α) → bind (meta α) (merge (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  merge/length l₁ l₂ = merge/clocked/length (length l₁ + length l₂) l₁ l₂

  merge/cost : cmp (Π pair λ _ → cost)
  merge/cost (l₁ , l₂) = merge/clocked/cost (length l₁ + length l₂) (l₁ , l₂)

  merge≤merge/cost : ∀ p → ub (list A) (merge p) (merge/cost p)
  merge≤merge/cost (l₁ , l₂) = merge/clocked≤merge/clocked/cost (length l₁ + length l₂) (l₁ , l₂)

  sort/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → F (list A))
  sort/clocked zero    l = ret l
  sort/clocked (suc k) l =
    bind (F (list A)) (split l) λ (l₁ , l₂) →
      bind (F (list A)) (sort/clocked k l₁) λ l₁' →
        bind (F (list A)) (sort/clocked k l₂) λ l₂' →
          merge (l₁' , l₂')

  sort/clocked/length : ∀ k l (κ : ℕ → α) → bind (meta α) (sort/clocked k l) (κ ∘ length) ≡ κ (length l)
  sort/clocked/length {_} zero    l κ = refl
  sort/clocked/length {α} (suc k) l κ =
    begin
      bnd (sort/clocked (suc k) l) (κ ∘ length)
    ≡⟨⟩
      bnd (split l) (λ (l₁ , l₂) → bnd (sort/clocked k l₁) (λ l₁' → bnd (sort/clocked k l₂) (λ l₂' → bnd (merge (l₁' , l₂')) (κ ∘ length))))
    ≡⟨ Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) → Eq.cong (bnd (sort/clocked k l₁)) (funext λ l₁' → Eq.cong (bnd (sort/clocked k l₂)) (funext λ l₂' → merge/length l₁' l₂' κ))) ⟩
      bnd (split l) (λ (l₁ , l₂) → bnd (sort/clocked k l₁) (λ l₁' → bnd (sort/clocked k l₂) (λ l₂' → κ (length l₁' + length l₂'))))
    ≡⟨ Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) → Eq.cong (bnd (sort/clocked k l₁)) (funext λ l₁' → sort/clocked/length k l₂ (λ n₂ → κ (length l₁' + n₂)))) ⟩
      bnd (split l) (λ (l₁ , l₂) → bnd (sort/clocked k l₁) (λ l₁' → κ (length l₁' + length l₂)))
    ≡⟨ Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) → sort/clocked/length k l₁ (λ n₁ → κ (n₁ + length l₂))) ⟩
      bnd (split l) (λ (l₁ , l₂) → κ (length l₁ + length l₂))
    ≡⟨ split/length l (λ n₁ n₂ → κ (n₁ + n₂)) ⟩
      κ (⌊ length l /2⌋ + ⌈ length l /2⌉ )
    ≡⟨ Eq.cong κ (⌊n/2⌋+⌈n/2⌉≡n (length l)) ⟩
      κ (length l)
    ∎
    where
      open ≡-Reasoning

      bnd : ∀ {A} → cmp (F A) → (val A → α) → α
      bnd = bind (meta α)

  sort/recurrence : ℕ → ℕ → ℕ
  sort/recurrence zero    n = zero
  sort/recurrence (suc k) n = sort/recurrence k ⌊ n /2⌋ + sort/recurrence k ⌈ n /2⌉ + n

  sort/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost k l = sort/recurrence k (length l)

  sort/clocked≤sort/clocked/cost : ∀ k l → ub (list A) (sort/clocked k l) (sort/clocked/cost k l)
  sort/clocked≤sort/clocked/cost zero l = ub/ret _
  sort/clocked≤sort/clocked/cost (suc k) l =
    Eq.subst (ub _ _) (Eq.sym (+-assoc (sort/recurrence k ⌊ length l /2⌋) _ _)) (
      Eq.subst (ub _ _) (Eq.cong (λ n → sort/recurrence k ⌊ length l /2⌋ + (sort/recurrence k ⌈ length l /2⌉ + n)) (⌊n/2⌋+⌈n/2⌉≡n _)) (
        Eq.subst (ub _ _) (split/length l (λ n₁ n₂ → sort/recurrence k n₁ + (sort/recurrence k n₂ + (n₁ + n₂)))) (
          ub/bind _ _ (split≤split/cost l) λ (l₁ , l₂) →
            Eq.subst (ub _ _) (sort/clocked/length k l₁ (λ n₁ → sort/recurrence k _ + (sort/recurrence k _ + (n₁ + _)))) (
              ub/bind _ _ (sort/clocked≤sort/clocked/cost k l₁) λ l₁' →
                Eq.subst (ub _ _) (sort/clocked/length k l₂ λ n₂ → sort/recurrence k _ + (_ + n₂)) (
                  ub/bind (sort/recurrence k _) _ (sort/clocked≤sort/clocked/cost k l₂) λ l₂' →
                    merge≤merge/cost (l₁' , l₂')
                )
            )
        )
      )
    )

  sort/depth : cmp (Π (list A) λ _ → meta ℕ)
  sort/depth l = let n = length l in aux n n ≤-refl
    where
      aux : (n : ℕ) → (m : ℕ) → Data.Nat._≤_ m n → ℕ
      aux _ zero _ = zero
      aux _ (suc zero) _ = zero
      aux (suc (suc n)) (suc (suc m)) (s≤s (s≤s h)) =
        suc (aux (suc n) (suc ⌈ m /2⌉) (s≤s (
          begin
            ⌈ m /2⌉
          ≤⟨ ⌈n/2⌉≤n m ⟩
            m
          ≤⟨ h ⟩
            n
          ∎
        )))
        where
          open ≤-Reasoning

  sort : cmp (Π (list A) λ _ → F (list A))
  sort l = sort/clocked (sort/depth l) l

  sort/correct : IsSort sort
  sort/correct = {!   !}

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost l = sort/clocked/cost (sort/depth l) l

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

module Ex/MergeSort where
  module Sort = MergeSort NatComparable

  list' = list (U (meta ℕ))

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ [])

  ex/merge : cmp (F list')
  ex/merge = Sort.merge (2 ∷ 3 ∷ 6 ∷ 8 ∷ [] , 1 ∷ 5 ∷ 8 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 32

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 32

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 47

module SortEquivalence (M : Comparable) where
  open Comparable M
  open Sorting M

  module ISort = InsertionSort M
  module MSort = MergeSort M

  unique-sorted : ∀ {l l'} → Sorted l → Sorted l' → l ↭ l' → l ≡ l'
  unique-sorted sorted sorted' refl = refl
  unique-sorted (_ ∷ sorted) (_ ∷ sorted') (prep x p) = Eq.cong (_∷_ x) (unique-sorted sorted sorted' p)
  unique-sorted ((h₁ ∷ _) ∷ (_ ∷ sorted)) ((h₂ ∷ _) ∷ (_ ∷ sorted')) (swap _ _ p) rewrite antisym h₁ h₂ =
    Eq.cong (λ l → _ ∷ _ ∷ l) (unique-sorted sorted sorted' p)
  unique-sorted sorted sorted' (trans {l} {l'} {l''} p₁ p₂) =
    begin
      l
    ≡⟨ unique-sorted sorted {!   !} p₁ ⟩
      l'
    ≡⟨ unique-sorted {!   !} sorted' p₂ ⟩
      l''
    ∎
      where open ≡-Reasoning
  -- unique-sorted sorted sorted' refl = refl
  -- unique-sorted (sorted-cons h sorted) (sorted-cons h' sorted') (prep x p) = Eq.cong (_∷_ x) (unique-sorted sorted sorted' p)
  -- unique-sorted (sorted-cons x (Sorting.sorted-cons x₅ sorted)) (Sorting.sorted-cons x₃ (Sorting.sorted-cons x₄ sorted')) (Sorting.swap x₁ x₂ p) = {!   !}
  -- unique-sorted sorted sorted' (trans p₁ p₂) = {!   !}
  -- unique-sorted {.[]} {.[]} sorted sorted' nil~ = refl
  -- unique-sorted {x ∷ l} {x ∷ l'} (sorted-cons _ sorted) (sorted-cons _ sorted') (cons~ p) = cong (_∷_ x) (unique-sorted sorted sorted' p)
  -- unique-sorted {x₂ ∷ x₁ ∷ l} {x₁ ∷ x₂ ∷ l} (sorted-cons (≤*-cons h _) _) (sorted-cons (≤*-cons h' _) _) swap~ =
  --   begin
  --     x₂ ∷ x₁ ∷ l
  --   ≡⟨ cong (_∷_ x₂) (cong (_∷ l) (antisym h' h)) ⟩
  --     x₂ ∷ x₂ ∷ l
  --   ≡⟨ cong (_∷ (x₂ ∷ l)) (antisym h h') ⟩
  --     x₁ ∷ x₂ ∷ l
  --   ∎
  --   where open ≡-Reasoning
  -- unique-sorted {l} {l''} sorted sorted'' (trans~ {l' = l'} p₁ p₂) =
  --   begin
  --     l
  --   ≡⟨ unique-sorted sorted {!   !} p₁ ⟩
  --     l'
  --   ≡⟨ unique-sorted {! sorted'  !} sorted'' p₂ ⟩
  --     l''
  --   ∎
  --   where open ≡-Reasoning

  isort≡msort : ◯ (ISort.sort ≡ MSort.sort)
  isort≡msort h =
    funext λ l →
      let (l'ᵢ , ≡ᵢ , ↭ᵢ , sortedᵢ) = ISort.sort/correct l in
      let (l'ₘ , ≡ₘ , ↭ₘ , sortedₘ) = MSort.sort/correct l in
      begin
        ISort.sort l
      ≡⟨ ≡ᵢ h ⟩
        ret l'ᵢ
      ≡⟨ Eq.cong ret (unique-sorted sortedᵢ sortedₘ (trans {ys = l} (↭-sym ↭ᵢ) ↭ₘ)) ⟩
        ret l'ₘ
      ≡⟨ Eq.sym (≡ₘ h) ⟩
        MSort.sort l
      ∎
        where open ≡-Reasoning
