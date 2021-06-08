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
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as Eq
open import Function
open import Data.Nat hiding (_≤_; _≤ᵇ_)
open import Data.Nat.Properties
open import Data.List using ([]; _∷_)

private
  variable
    α : Set

module List where
  private
    variable
      A : tp pos

  postulate
    list : tp pos → tp pos
    nil : val (list A)
    cons : val A → val (list A) → val (list A)

    list/ind : (l : val (list A)) → (X : val (list A) → tp neg) → cmp (X nil) →
      ((a : val A) → (l : val (list A)) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      cmp (X l)
    list/ind/nil : ∀ {X} → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val ((list A))) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      list/ind nil X e0 e1 ≡ e0
    {-# REWRITE list/ind/nil #-}
    list/ind/cons : ∀ {X} → (a : val A) → (l : val ((list A))) → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val ((list A))) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      list/ind (cons a l) X e0 e1 ≡ e1 a l (list/ind l X e0 e1)
    {-# REWRITE list/ind/cons #-}

  list/match : (l : val (list A)) → (X : val (list A) → tp neg) → cmp (X nil) →
    ((a : val A) → (l : val (list A)) → cmp (X (cons a l))) →
    cmp (X l)
  list/match l X e0 e1 = list/ind l X e0 (λ a l _ → e1 a l)

  of-list : {α : Set} → (α → val A) → Data.List.List α → val (list A)
  of-list f []       = nil
  of-list f (x ∷ xs) = cons (f x) (of-list f xs)

  length : val (list A) → cmp (meta ℕ)
  length l = list/ind l (λ _ → meta ℕ) zero λ _ _ → suc

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
    reflects : ∀ m n {q} b → m ≤ᵇ n ≡ step' (F bool) q (ret b) → Reflects (m ≤ n) b
    antisym : Antisymmetric _≡_ _≤_
    h-cost : {x y : val A} → ub bool (x ≤ᵇ y) 1

NatComparable : Comparable
NatComparable = record
  { A = nat
  ; _≤_ = λ m n → {!   !} ≤ {!   !}
  ; _≤ᵇ_ = λ m n → step' (F bool) 1 (ret (Nat.toℕ m ≤ᵇ Nat.toℕ n))
  ; reflects = {!   !}
  ; antisym = {!   !}
  ; h-cost = ub/step/suc 0 (ub/ret 0)
  }
  where open Data.Nat

cost = meta ℕ

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module InsertionSort (M : Comparable) where
  open Comparable M
  open List

  insert : cmp (Π A λ _ → Π (list A) λ _ → F (list A))
  insert x l = list/ind l (λ _ → F (list A)) (ret (cons x nil)) inductive-step
    where
      inductive-step : val A → val (list A) → cmp (F (list A)) → cmp (F (list A))
      inductive-step y ys ys' = bind (F (list A)) (x ≤ᵇ y)
        λ { false → bind (F (list A)) ys' (ret ∘ cons y)
          ; true  → ret (cons x (cons y ys)) }

  insert/length : ∀ {α} x l (κ : ℕ → α) → bind (meta α) (insert x l) (κ ∘ length) ≡ κ (suc (length l))
  insert/length {α} x l = list/ind l (λ _ → meta _) (λ _ → refl) inductive-step
    where
      inductive-step : (y : val A) (ys : val (list A)) →
        (∀ κ → bind (meta α) (insert x         ys ) (κ ∘ length) ≡ κ (suc (length         ys ))) →
        (∀ κ → bind (meta α) (insert x (cons y ys)) (κ ∘ length) ≡ κ (suc (length (cons y ys))))
      inductive-step y ys h κ with h-cost {x} {y}
      ... | ub/intro false _ h-eq rewrite eq/ref h-eq = h (κ ∘ suc)
      ... | ub/intro true  _ h-eq rewrite eq/ref h-eq = refl

  insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost _ = length

  insert≤insert/cost : ∀ x l → ub (list A) (insert x l) (insert/cost x l)
  insert≤insert/cost x l = list/ind l (λ _ → meta _) (ub/ret zero) inductive-step
    where
      inductive-step : (y : val A) (ys : val (list A)) →
        ub (list A) (insert x         ys ) (length         ys ) →
        ub (list A) (insert x (cons y ys)) (length (cons y ys))
      inductive-step y ys h with h-cost {x} {y}
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
                (ub/bind/const _ _ (ub/step (length ys) q h) λ _ → ub/ret zero)
                where open ≤-Reasoning

  sort : cmp (Π (list A) λ _ → F (list A))
  sort l = list/ind l (λ _ → F (list A)) (ret nil) λ x _ ys → bind (F (list A)) ys (insert x)

  sort/length : ∀ {α} l (κ : ℕ → α) → bind (meta α) (sort l) (κ ∘ length) ≡ κ (length l)
  sort/length {α} l = list/ind l (λ l → meta (∀ κ → bind (meta α) (sort l) (κ ∘ length) ≡ κ (length l))) (λ _ → refl) inductive-step
    where
      inductive-step : (x : val A) (xs : val (list A)) →
        (∀ κ → bind (meta α) (sort         xs ) (κ ∘ length) ≡ κ (length         xs )) →
        (∀ κ → bind (meta α) (sort (cons x xs)) (κ ∘ length) ≡ κ (length (cons x xs)))
      inductive-step x xs h κ =
        begin
          bind (meta α) (sort (cons x xs)) (κ ∘ length)
        ≡⟨⟩
          bind (meta α) (bind (F (list A)) (sort xs) (insert x)) (κ ∘ length)
        ≡⟨⟩
          bind (meta α) (sort xs) (λ xs' → bind (meta α) (insert x xs') (κ ∘ length))
        ≡⟨ Eq.cong (bind (meta α) (sort xs)) (funext λ xs' → insert/length x xs' κ)  ⟩
          bind (meta α) (sort xs) (λ xs' → κ (suc (length xs')))
        ≡⟨ h (κ ∘ suc) ⟩
          κ (length (cons x xs))
        ∎
          where open ≡-Reasoning

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost l = list/ind l (λ _ → meta ℕ) zero (λ x xs c → c + insert/cost x xs)

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = list/ind l (λ _ → meta _) (ub/ret zero) inductive-step
    where
      inductive-step : (x : val A) (xs : val (list A)) →
        cmp (meta (ub (list A) (sort         xs ) (sort/cost         xs ))) →
        cmp (meta (ub (list A) (sort (cons x xs)) (sort/cost (cons x xs))))
      inductive-step x xs h with ub/bind (sort/cost xs) length h (insert≤insert/cost x)
      ... | h-bind rewrite sort/length xs (_+_ (sort/cost xs)) = h-bind

module Ex/InsertionSort where
  module Sort = InsertionSort NatComparable

  list = List.list nat
  of-list = List.of-list {A = Nat.nat} Nat.tonat

  ex/insert : cmp (F list)
  ex/insert = Sort.insert (Nat.tonat 3) (of-list (1 ∷ 2 ∷ 4 ∷ []))

  ex/sort : cmp (F list)
  ex/sort = Sort.sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))

  ex/sort/forward : cmp (F list)
  ex/sort/forward = Sort.sort (of-list test/forward)  -- cost: 15

  ex/sort/backward : cmp (F list)
  ex/sort/backward = Sort.sort (of-list test/backward)  -- cost: 120

  ex/sort/shuffled : cmp (F list)
  ex/sort/shuffled = Sort.sort (of-list test/shuffled)  -- cost: 76

module Append where
  private
    variable
      A : tp pos

  open List

  append : cmp (Π (list A) λ _ → Π (list A) λ _ → F (list A))
  append {A} l₁ l₂ =
    list/ind l₁ (λ _ → F (list A))
      (ret l₂)
      λ hd _ tl → bind (F (list A)) tl (λ tl → ret (cons hd tl))

  append/length : ∀ {α : Set} (l₁ l₂ : val (list A)) (κ : ℕ → α) →
    bind (meta α) (append l₁ l₂) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  append/length {A} {α} l₁ l₂ =
    list/ind l₁
      (λ l₁ → meta (∀ κ → bind _ (append l₁ l₂) (κ ∘ length) ≡ κ (length l₁ + length l₂)))
      (λ κ → refl)
      λ _ _ h κ → h (κ ∘ suc)

  append/cost : cmp (Π (list A) λ _ → Π (list A) λ _ → cost)
  append/cost _ _ = zero

  append≤append/cost : ∀ l₁ l₂ → ub (list A) (append l₁ l₂) (append/cost l₁ l₂)
  append≤append/cost {A} l₁ l₂ =
    list/ind l₁ (λ l₁ → meta (ub (list A) (append l₁ l₂) (append/cost l₁ l₂)))
      (ub/ret _)
      λ x xs h → ub/bind/const zero zero h λ _ → ub/ret _

module MergeSort (M : Comparable) where
  open Comparable M
  open List

  pair = Σ++ (list A) λ _ → (list A)

  split/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → F pair)
  split/clocked zero    l = ret (nil , l)
  split/clocked (suc k) l =
    list/match l (λ _ → F pair) (ret (nil , nil)) λ x xs →
      bind (F pair) (split/clocked k xs) λ (l₁ , l₂) →
        ret (cons x l₁ , l₂)

  split/clocked/length : ∀ {α} k k' l → k + k' ≡ length l → (κ : ℕ → ℕ → α) →
    bind (meta α) (split/clocked k l) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ k k'
  split/clocked/length {α} zero    _  l = λ { refl _ → refl }
  split/clocked/length {α} (suc k) k' l =
    list/match l (λ l → meta (suc k + k' ≡ length l → ∀ κ → bind _ (split/clocked (suc k) l) _ ≡ _))
      (λ ())
      λ x xs h κ → split/clocked/length k k' xs (suc-injective h) (κ ∘ suc)

  split/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  split/clocked/cost _ _ = zero

  split/clocked≤split/clocked/cost : ∀ k l → ub pair (split/clocked k l) (split/clocked/cost k l)
  split/clocked≤split/clocked/cost zero    l = ub/ret _
  split/clocked≤split/clocked/cost (suc k) l =
    list/match l (λ l → meta (ub pair (split/clocked (suc k) l) (split/clocked/cost (suc k) l)))
      (ub/ret _)
      λ x xs → ub/bind/const zero zero (split/clocked≤split/clocked/cost k xs) λ _ → ub/ret _

  split : cmp (Π (list A) λ _ → F pair)
  split l = split/clocked ⌊ length l /2⌋ l

  split/length : ∀ {α} l (κ : ℕ → ℕ → α) →
    bind (meta α) (split l) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ ⌊ length l /2⌋ ⌈ length l /2⌉
  split/length {α} l = split/clocked/length ⌊ length l /2⌋ ⌈ length l /2⌉ l (⌊n/2⌋+⌈n/2⌉≡n (length l))

  split/cost : cmp (Π (list A) λ _ → cost)
  split/cost l = split/clocked/cost ⌊ length l /2⌋ l

  split≤split/cost : ∀ l → ub pair (split l) (split/cost l)
  split≤split/cost l = split/clocked≤split/clocked/cost ⌊ length l /2⌋ l

  merge/clocked : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → F (list A))
  merge/clocked zero    (l₁ , l₂) = Append.append l₁ l₂
  merge/clocked (suc k) (l₁ , l₂) =
    list/match l₁ (λ _ → F (list A))
      (ret l₂)
      λ x xs →
        list/match l₂ (λ _ → F (list A))
          (ret l₁)
          λ y ys →
            bind (F (list A)) (x ≤ᵇ y)
              λ { false → bind (F (list A)) (merge/clocked k (cons x xs , ys)) (ret ∘ cons y)
                ; true  → bind (F (list A)) (merge/clocked k (xs , cons y ys)) (ret ∘ cons x) }

  merge/clocked/length : ∀ {α} k (l₁ l₂ : val (list A)) (κ : ℕ → α) →
    bind (meta α) (merge/clocked k (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  merge/clocked/length {_} zero    l₁ l₂ κ = Append.append/length l₁ l₂ κ
  merge/clocked/length {α} (suc k) l₁ l₂ κ =
    list/match l₁ (λ l₁ → meta (bind _ (merge/clocked (suc k) (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)))
      refl
      λ x xs →
        list/match l₂ (λ l₂ → meta (bind _ (merge/clocked (suc k) (cons x xs , l₂)) _ ≡ κ (length (cons x xs) + length l₂)))
          (Eq.cong (κ ∘ suc) (sym (+-identityʳ (length xs))))
          λ y ys →
            inductive-step x xs y ys
    where
      open ≡-Reasoning

      inductive-step : (x : val A) (xs : val (list A)) (y : val A) (ys : val (list A)) →
        bind (meta α) (merge/clocked (suc k) (cons x xs , cons y ys)) (κ ∘ length) ≡ κ (length (cons x xs) + length (cons y ys))
      inductive-step x xs y ys with h-cost {x} {y}
      ... | ub/intro false _ h-eq rewrite eq/ref h-eq =
        begin
          bind (meta α) (merge/clocked k (cons x xs , ys)) (λ l → bind (meta α) (ret {list A} (cons y l)) (κ ∘ length))
        ≡⟨⟩
          bind (meta α) (merge/clocked k (cons x xs , ys)) (λ l → (κ ∘ length) (cons y l))
        ≡⟨⟩
          bind (meta α) (merge/clocked k (cons x xs , ys)) (λ l → (κ ∘ suc) (length l))
        ≡⟨ merge/clocked/length k (cons x xs) ys (κ ∘ suc) ⟩
          κ (suc (length (cons x xs) + length ys))
        ≡⟨ Eq.cong κ (sym (+-suc (length (cons x xs)) (length ys))) ⟩
          κ (length (cons x xs) + length (cons y ys))
        ∎
      ... | ub/intro true  _ h-eq rewrite eq/ref h-eq =
        begin
          bind (meta α) (merge/clocked k (xs , cons y ys)) (λ l → bind (meta α) (ret {list A} (cons x l)) (κ ∘ length))
        ≡⟨⟩
          bind (meta α) (merge/clocked k (xs , cons y ys)) (λ l → (κ ∘ length) (cons x l))
        ≡⟨⟩
          bind (meta α) (merge/clocked k (xs , cons y ys)) (λ l → (κ ∘ suc) (length l))
        ≡⟨ merge/clocked/length k xs (cons y ys) (κ ∘ suc) ⟩
          κ (suc (length xs + length (cons y ys)))
        ≡⟨⟩
          κ (length (cons x xs) + length (cons y ys))
        ∎

  merge/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → cost)
  merge/clocked/cost k _ = k

  merge/clocked≤merge/clocked/cost : ∀ k p → ub (list A) (merge/clocked k p) (merge/clocked/cost k p)
  merge/clocked≤merge/clocked/cost zero    (l₁ , l₂) = Append.append≤append/cost l₁ l₂
  merge/clocked≤merge/clocked/cost (suc k) (l₁ , l₂) =
    list/match l₁ (λ l₁ → meta (ub (list A) (merge/clocked (suc k) (l₁ , l₂)) (merge/clocked/cost (suc k) (l₁ , l₂))))
      (ub/ret _)
      λ x xs →
        list/match l₂ (λ l₂ → meta (ub (list A) (merge/clocked (suc k) (cons x xs , l₂)) (merge/clocked/cost (suc k) (cons x xs , l₂))))
          (ub/ret _)
          λ y ys →
            ub/bind/const 1 k h-cost 
              λ { false → ub/bind/const' k zero (+-identityʳ k) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret _
                ; true  → ub/bind/const' k zero (+-identityʳ k) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret _ }

  merge : cmp (Π pair λ _ → F (list A))
  merge (l₁ , l₂) = merge/clocked (length l₁ + length l₂) (l₁ , l₂)

  merge/length : ∀ {α} l₁ l₂ (κ : ℕ → α) → bind (meta α) (merge (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
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

  sort/clocked/length : ∀ {α} k l (κ : ℕ → α) → bind (meta α) (sort/clocked k l) (κ ∘ length) ≡ κ (length l)
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
    subst (ub _ _) (sym (+-assoc (sort/recurrence k ⌊ length l /2⌋) _ _)) (
      subst (ub _ _) (Eq.cong (λ n → sort/recurrence k ⌊ length l /2⌋ + (sort/recurrence k ⌈ length l /2⌉ + n)) (⌊n/2⌋+⌈n/2⌉≡n _)) (
        subst (ub _ _) (split/length l (λ n₁ n₂ → sort/recurrence k n₁ + (sort/recurrence k n₂ + (n₁ + n₂)))) (
          ub/bind _ _ (split≤split/cost l) λ (l₁ , l₂) →
            subst (ub _ _) (sort/clocked/length k l₁ (λ n₁ → sort/recurrence k _ + (sort/recurrence k _ + (n₁ + _)))) (
              ub/bind _ _ (sort/clocked≤sort/clocked/cost k l₁) λ l₁' →
                subst (ub _ _) (sort/clocked/length k l₂ λ n₂ → sort/recurrence k _ + (_ + n₂)) (
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

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost l = sort/clocked/cost (sort/depth l) l

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

module Ex/MergeSort where
  module Sort = MergeSort NatComparable

  list = List.list nat
  of-list = List.of-list {A = Nat.nat} Nat.tonat

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (of-list (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ []))

  ex/merge : cmp (F list)
  ex/merge = Sort.merge (of-list (2 ∷ 3 ∷ 6 ∷ 8 ∷ []) , of-list (1 ∷ 5 ∷ 8 ∷ []))

  ex/sort : cmp (F list)
  ex/sort = Sort.sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))

  ex/sort/forward : cmp (F list)
  ex/sort/forward = Sort.sort (of-list test/forward)  -- cost: 32

  ex/sort/backward : cmp (F list)
  ex/sort/backward = Sort.sort (of-list test/backward)  -- cost: 32

  ex/sort/shuffled : cmp (F list)
  ex/sort/shuffled = Sort.sort (of-list test/shuffled)  -- cost: 47

module SortEquivalence (M : Comparable) where
  open Comparable M
  open List

  module ISort = InsertionSort M
  module MSort = MergeSort M

  open import Data.Product

  data _≤*_ (x : val A) : val (list A) → Set where
    ≤*-nil  : x ≤* nil
    ≤*-cons : ∀ {y ys} → x ≤ y → x ≤* ys → x ≤* (cons y ys)

  data Sorted : val (list A) → Set where
    sorted-nil : Sorted nil
    sorted-cons : ∀ {y ys} → y ≤* ys → Sorted (cons y ys)

  data _~_ : val (list A) → val (list A) → Set where
    nil~ : nil ~ nil
    cons~ : ∀ {l l' x} → l ~ l' → cons x l ~ cons x l'
    swap~ : ∀ {x₁ x₂ l} → cons x₂ (cons x₁ l) ~ cons x₁ (cons x₂ l)
    trans~ : ∀ {l l' l''} → l ~ l' → l' ~ l'' → l ~ l''

  SortedOf : val (list A) → val (list A) → Set
  SortedOf l l' = l ~ l' × Sorted l'

  unique-sorted : ∀ {l l'₁ l'₂} → SortedOf l l'₁ → SortedOf l l'₂ → l'₁ ≡ l'₂
  unique-sorted (~₁ , sorted₁) (~₂ , sorted₂) = {!   !}

  isort-correct : ∀ l → ∃ λ l' → ∃ λ q → ISort.sort l ≡ step' (F (list A)) q (ret l') × SortedOf l l'
  isort-correct = {!   !}

  msort-correct : ∀ l → ∃ λ l' → ∃ λ q → MSort.sort l ≡ step' (F (list A)) q (ret l') × SortedOf l l'
  msort-correct = {!   !}

  isort≡msort : ◯ (ISort.sort ≡ MSort.sort)
  isort≡msort h =
    funext λ l →
      let (l'ᵢ , qᵢ , ≡ᵢ , hᵢ) = isort-correct l in
      let (l'ₘ , qₘ , ≡ₘ , hₘ) = msort-correct l in
      begin
        ISort.sort l
      ≡⟨ ≡ᵢ ⟩
        step' (F (list A)) qᵢ (ret l'ᵢ)
      ≡⟨ step'/ext (F (list A)) (ret l'ᵢ) qᵢ h ⟩
        ret l'ᵢ
      ≡⟨ Eq.cong ret (unique-sorted hᵢ hₘ) ⟩
        ret l'ₘ
      ≡⟨ sym (step'/ext (F (list A)) (ret l'ₘ) qₘ h) ⟩
        step' (F (list A)) qₘ (ret l'ₘ)
      ≡⟨ sym ≡ₘ ⟩
        MSort.sort l
      ∎
      where open ≡-Reasoning
