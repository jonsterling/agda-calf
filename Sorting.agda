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
  postulate
    bool : tp pos
    bool/decode : val bool ≡ Data.Bool.Bool
    {-# REWRITE bool/decode #-}

cost = meta ℕ

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module InsertionSort
  (A : tp pos)
  (_≤ᵇ_ : val A → val A → cmp (F Bool.bool))
  (h-cost : {x y : val A} → ub Bool.bool (x ≤ᵇ y) 1)
  where
  open List
  open Bool

  insert : cmp (Π A λ _ → Π (list A) λ _ → F (list A))
  insert x l = list/ind l (λ _ → F (list A)) (ret (cons x nil)) inductive-step
    where
      inductive-step : val A → val (list A) → cmp (F (list A)) → cmp (F (list A))
      inductive-step y ys ys' = bind (F (list A)) (x ≤ᵇ y)
        λ { false → bind (F (list A)) ys' (ret ∘ cons y)
          ; true  → ret (cons x (cons y ys)) }

  insert/length : ∀ {α} x l (k : ℕ → α) → bind (meta α) (insert x l) (k ∘ length) ≡ k (suc (length l))
  insert/length {α} x l = list/ind l (λ _ → meta _) (λ _ → refl) inductive-step
    where
      inductive-step : (y : val A) (ys : val (list A)) →
        (∀ k → bind (meta α) (insert x         ys ) (k ∘ length) ≡ k (suc (length         ys ))) →
        (∀ k → bind (meta α) (insert x (cons y ys)) (k ∘ length) ≡ k (suc (length (cons y ys))))
      inductive-step y ys h k with h-cost {x} {y}
      ... | ub/intro false _ h-eq rewrite eq/ref h-eq =
        begin
          bind _ (bind (F (list A)) (insert x ys) (ret ∘ cons y)) (k ∘ length)
        ≡⟨ bind/assoc {B = (list A)} {C = meta α} {e = insert x ys} {f1 = ret ∘ cons y} {f2 = k ∘ length} ⟩
          bind _ (insert x ys) (λ ys' → bind {A = (list A)} (meta α) (ret (cons y ys')) (k ∘ length))
        ≡⟨ Eq.cong (bind {A = (list A)} _ (insert x ys)) (funext λ ys' → sym (bind/ret {A = (list A)} {X = meta α} {v = cons y ys'} {f = k ∘ length})) ⟩
          bind _ (insert x ys) (k ∘ length ∘ cons y)
        ≡⟨ h (k ∘ suc) ⟩
          k (suc (length (cons y ys)))
        ∎
          where open ≡-Reasoning
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

  sort/length : ∀ {α} l (k : ℕ → α) → bind (meta α) (sort l) (k ∘ length) ≡ k (length l)
  sort/length {α} l = list/ind l (λ l → meta (∀ k → bind (meta α) (sort l) (k ∘ length) ≡ k (length l))) (λ _ → refl) inductive-step
    where
      inductive-step : (x : val A) (xs : val (list A)) →
        (∀ k → bind (meta α) (sort         xs ) (k ∘ length) ≡ k (length         xs )) →
        (∀ k → bind (meta α) (sort (cons x xs)) (k ∘ length) ≡ k (length (cons x xs)))
      inductive-step x xs h k =
        begin
          bind (meta α) (sort (cons x xs)) (k ∘ length)
        ≡⟨⟩
          bind (meta α) (bind (F (list A)) (sort xs) (insert x)) (k ∘ length)
        ≡⟨ bind/assoc {B = (list A)} {C = meta α} {e = sort xs} {f1 = insert x} ⟩
          bind (meta α) (sort xs) (λ xs' → bind (meta α) (insert x xs') (k ∘ length))
        ≡⟨ Eq.cong (bind (meta α) (sort xs)) (funext λ xs' → insert/length x xs' k)  ⟩
          bind (meta α) (sort xs) (λ xs' → k (suc (length xs')))
        ≡⟨ h (k ∘ suc) ⟩
          k (length (cons x xs))
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
      inductive-step x xs h with ub/bind {e = sort xs} (sort/cost xs) length h (insert≤insert/cost x)
      ... | h-bind rewrite sort/length xs (_+_ (sort/cost xs)) = h-bind

module Ex/InsertionSort where
  module Sort =
    InsertionSort
      Nat.nat
      (λ m n → step' (F Bool.bool) 1 (ret (Nat.toℕ m ≤ᵇ Nat.toℕ n)))
      (ub/step/suc 0 (ub/ret 0))

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

module MergeSort
  (A : tp pos)
  (_≤ᵇ_ : val A → val A → cmp (F Bool.bool))
  (h-cost : {x y : val A} → ub Bool.bool (x ≤ᵇ y) 1)
  where
  open List
  open Bool

  pair = Σ++ (list A) λ _ → (list A)

  module Option where
    option : tp pos → tp pos
    option A = sum A unit

    some : ∀ {A} → val A → val (option A)
    some = inj₁

    none : ∀ {A} → val (option A)
    none = inj₂ triv

    option/case : ∀ A (X : val (option A) → tp neg) → (s : val (option A)) → ((a : val A) → cmp (X (some {A} a))) → (cmp (X (none {A}))) → cmp (X s)
    option/case A X s b₁ b₂ = sum/case A unit X s b₁ (λ { triv → b₂ })

    ub/option/case/const/const : ∀ A (C : val (option A) → tp pos) →
      (s : val (option A)) →
      (e0 : (a : val A) → cmp (F (C (some {A} a)))) →
      (e1 : cmp (F (C (none {A})))) →
      (p : ℕ) →
      ((a : val A) → ub (C (some {A} a)) (e0 a) p) →
      (ub (C (none {A})) e1 p) →
      ub (C s) (option/case A (λ s → F (C s)) s e0 e1) p
    ub/option/case/const/const A C s e0 e1 p h1 h2 = ub/sum/case/const/const A unit C s e0 (λ { triv → e1 }) p h1 (λ { triv → h2 })

  option = Option.option A
  none = Option.none {A}
  some = Option.some {A}
  option/case = Option.option/case A
  ub/option/case = Option.ub/option/case/const/const A

  split/aux/o = Σ++ option λ _ → pair

  split/aux : cmp (Π (list A) λ _ → F split/aux/o)
  split/aux l =
    list/ind l (λ _ → F split/aux/o)
      (ret (none , nil , nil))
      λ x _ acc → bind (F _) acc λ { (opt , xs , ys) →
        option/case (λ _ → F _) opt
          (λ y → ret (none , cons x xs , cons y ys))
          (ret (some x , xs , ys))
      }

  split/aux/cost : cmp (Π (list A) λ _ → cost)
  split/aux/cost _ = zero

  split/aux≤split/aux/cost : ∀ l → ub split/aux/o (split/aux l) (split/aux/cost l)
  split/aux≤split/aux/cost l =
    list/ind l (λ l → meta (ub split/aux/o (split/aux l) (split/aux/cost l)))
      (ub/ret _)
      λ _ _ h → ub/bind/const zero _ h λ { (opt , _) → ub/option/case
        (λ _ → _) opt _ _ _ (λ _ → ub/ret _) (ub/ret _)
      }

  split : cmp (Π (list A) λ _ → F pair)
  split l =
    bind (F pair) (split/aux l)
      λ { (opt , xs , ys) →
        option/case (λ _ → F pair) opt
          (λ x → ret (cons x xs , ys))
          (ret (xs , ys))
      }

  split/cost : cmp (Π (list A) λ _ → cost)
  split/cost _ = zero

  split≤split/cost : ∀ l → ub pair (split l) (split/cost l)
  split≤split/cost l =
    ub/bind/const zero _ (split/aux≤split/aux/cost l) λ { (opt , _) →
      ub/option/case _ opt _ _ _ (λ _ → ub/ret _) (ub/ret _)
    }

  merge/clocked : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → F (list A))
  merge/clocked zero    _         = ret nil
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

  merge/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → cost)
  merge/clocked/cost n _ = n

  merge/clocked≤merge/clocked/cost : ∀ n p → ub (list A) (merge/clocked n p) (merge/clocked/cost n p)
  merge/clocked≤merge/clocked/cost zero _ = ub/ret _
  merge/clocked≤merge/clocked/cost (suc n) (l₁ , l₂) =
    list/match l₁ (λ l₁ → meta (ub (list A) (merge/clocked (suc n) (l₁ , l₂)) (merge/clocked/cost (suc n) (l₁ , l₂))))
      (ub/ret _)
      λ x xs →
        list/match l₂ (λ l₂ → meta (ub (list A) (merge/clocked (suc n) (cons x xs , l₂)) (merge/clocked/cost (suc n) (cons x xs , l₂))))
          (ub/ret _)
          λ y ys →
            ub/bind/const 1 n h-cost 
              λ { false → ub/bind/const' n zero (+-identityʳ n) (merge/clocked≤merge/clocked/cost n _) λ _ → ub/ret _
                ; true  → ub/bind/const' n zero (+-identityʳ n) (merge/clocked≤merge/clocked/cost n _) λ _ → ub/ret _ }

  merge : cmp (Π pair λ _ → F (list A))
  merge (l₁ , l₂) = merge/clocked (length l₁ + length l₂) (l₁ , l₂)

  merge/cost : cmp (Π pair λ _ → cost)
  merge/cost (l₁ , l₂) = length l₁ + length l₂

  merge≤merge/cost : ∀ p → ub (list A) (merge p) (merge/cost p)
  merge≤merge/cost (l₁ , l₂) = merge/clocked≤merge/clocked/cost (length l₁ + length l₂) (l₁ , l₂)

  sort/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → F (list A))
  sort/clocked zero    l = ret l
  sort/clocked (suc k) l =
    bind (F (list A)) (split l) λ { (l₁ , l₂) →
      bind (F (list A)) (sort/clocked k l₁) λ l₁' →
        bind (F (list A)) (sort/clocked k l₂) λ l₂' →
          merge (l₁' , l₂')
    }

  sort/depth : cmp (Π (list A) λ _ → meta ℕ)
  sort/depth l = let n = length l in aux n n ≤-refl
    where
      aux : (n : ℕ) → (m : ℕ) → m ≤ n → ℕ
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
       where open ≤-Reasoning

  sort : cmp (Π (list A) λ _ → F (list A))
  sort l = sort/clocked (sort/depth l) l

module Ex/MergeSort where
  module Sort =
    MergeSort
      Nat.nat
      (λ m n → step' (F Bool.bool) 1 (ret (Nat.toℕ m ≤ᵇ Nat.toℕ n)))
      (ub/step/suc 0 (ub/ret 0))

  list = List.list nat
  of-list = List.of-list {A = Nat.nat} Nat.tonat

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (of-list (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ []))

  ex/merge : cmp (F list)
  ex/merge = Sort.merge (of-list (2 ∷ 3 ∷ 6 ∷ 8 ∷ []) , of-list (1 ∷ 5 ∷ 8 ∷ []))

  ex/sort : cmp (F list)
  ex/sort = Sort.sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))

  ex/sort/forward : cmp (F list)
  ex/sort/forward = Sort.sort (of-list test/forward)

  ex/sort/backward : cmp (F list)
  ex/sort/backward = Sort.sort (of-list test/backward)

  ex/sort/shuffled : cmp (F list)
  ex/sort/shuffled = Sort.sort (of-list test/shuffled)
