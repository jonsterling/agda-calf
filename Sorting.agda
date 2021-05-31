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

    ff tt : val bool

    bool/if : (X : val bool → tp neg) (b : val bool) → cmp (X tt) → cmp (X ff) → cmp (X b)

    if/tt : ∀ {X} → (e1 : cmp (X tt)) → (e2 : cmp (X ff)) → bool/if X tt e1 e2 ≡ e1
    if/ff : ∀ {X} → (e1 : cmp (X tt)) → (e2 : cmp (X ff)) → bool/if X ff e1 e2 ≡ e2
    {-# REWRITE if/tt if/ff #-}

    bool/decode : val bool ≡ Data.Bool.Bool
    {-# REWRITE bool/decode #-}

    bool/decode/ff : ff ≡ false
    bool/decode/tt : tt ≡ true
    {-# REWRITE bool/decode/ff bool/decode/tt #-}

cost = meta ℕ

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

  insert/length : ∀ x l → bind (meta ℕ) (insert x l) length ≡ suc (length l)
  insert/length x l = list/ind l (λ _ → meta _) refl inductive-step
    where
      inductive-step : (y : val A) (ys : val (list A)) →
        (bind (meta ℕ) (insert x         ys ) length ≡ suc (length         ys )) →
        (bind (meta ℕ) (insert x (cons y ys)) length ≡ suc (length (cons y ys)))
      inductive-step y ys h with h-cost {x} {y}
      ... | ub/intro false _ h-eq rewrite eq/ref h-eq =
        begin
          bind _ (bind (F (list A)) (insert x ys) (ret ∘ cons y)) length
        ≡⟨ bind/assoc {B = (list A)} {C = meta ℕ} {e = insert x ys} {f1 = ret ∘ cons y} {f2 = length} ⟩
          bind _ (insert x ys) (λ ys' → bind {A = (list A)} (meta ℕ) (ret (cons y ys')) length)
        ≡⟨ Eq.cong (bind {A = (list A)} (meta ℕ) (insert x ys)) (funext λ ys' → sym (bind/ret {A = (list A)} {X = meta ℕ} {v = cons y ys'} {f = length})) ⟩
          bind _ (insert x ys) (length ∘ cons y)
        ≡⟨ Eq.sym (bind/meta (list A) ℕ ℕ (insert x ys) length suc) ⟩
          suc (bind (meta ℕ) (insert x ys) length)
        ≡⟨ Eq.cong suc h ⟩
          suc (length (cons y ys))
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

  -- ex-insert : cmp (F (list A))
  -- ex-insert = insert (Nat.tonat 3) (of-list (1 ∷ 2 ∷ 4 ∷ []))

  sort : cmp (Π (list A) λ _ → F (list A))
  sort l = list/ind l (λ _ → F (list A)) (ret nil) λ x _ ys → bind (F (list A)) ys (insert x)

  sort/length : ∀ l → bind (meta ℕ) (sort l) length ≡ length l
  sort/length l = list/ind l (λ l → meta (bind (meta ℕ) (sort l) length ≡ length l)) refl inductive-step
    where
      inductive-step : (x : val A) (xs : val (list A)) →
        (bind (meta ℕ) (sort         xs ) length ≡ length         xs ) →
        (bind (meta ℕ) (sort (cons x xs)) length ≡ length (cons x xs))
      inductive-step x xs h =
        begin
          bind (meta ℕ) (sort (cons x xs)) length
        ≡⟨⟩
          bind (meta ℕ) (bind (F (list A)) (sort xs) (insert x)) length
        ≡⟨ bind/assoc {B = (list A)} {C = meta ℕ} {e = sort xs} {f1 = insert x} ⟩
          bind (meta ℕ) (sort xs) (λ xs' → bind (meta ℕ) (insert x xs') length)
        ≡⟨ Eq.cong (bind (meta ℕ) (sort xs)) (funext λ xs' → insert/length x xs')  ⟩
          bind (meta ℕ) (sort xs) (λ xs' → suc (length xs'))
        ≡⟨ Eq.sym (bind/meta (list A) ℕ ℕ (sort xs) length suc)  ⟩
          suc (bind (meta ℕ) (sort xs) length)
        ≡⟨ Eq.cong suc h  ⟩
          length (cons x xs)
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
      inductive-step x xs h =
        let foo = ub/bind {e = sort xs} (sort/cost xs) length h (insert≤insert/cost x)
        in {!   !} -- subst {!   !} (sym (bind/meta {!   !} {!   !} {!   !} (sort xs) (insert x) {!   !})) {!   !}
        -- ub/step/suc
        --   (length xs + sort/cost xs)
        --   (ub/bind/const {e = {!   !}} {!   !} {! length xs  !} {!   !} {!   !})
      --  with ub/step/suc _ (ub/bind (sort/cost xs) (insert/cost x) h (insert≤insert/cost x))
      -- ... | h-step rewrite sort/length xs = {! h-step  !} --  rewrite sort/length xs (_+_ (sort/cost xs)) | +-comm (sort/cost xs) (length xs) = h-step

  -- ex-sort : cmp (F (list A))
  -- ex-sort = sort (of-list (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ []))

ex/insert : cmp (F (List.list nat))
ex/insert = Sort.insert (Nat.tonat 3) (List.of-list Nat.tonat (1 ∷ 2 ∷ 4 ∷ []))
  where
    module Sort =
      InsertionSort
        Nat.nat
        (λ m n → ret (Nat.toℕ m ≤ᵇ Nat.toℕ n))
        (ub/ret 1)
