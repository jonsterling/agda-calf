{-# OPTIONS --prop --rewriting #-}

module Sorting where

open import Prelude using (funext)
open import Metalanguage
open import Upper
open import Refinement
open import Eq
open import PhaseDistinction
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Properties as N using (module ≤-Reasoning)

private
  variable
    α : Set

module List where
  open import Data.List public using (List; []; _∷_; [_]; length; _++_)
  open import Data.List.Properties public

  list : tp pos → tp pos
  list A = U (meta (List (val A)))

open List

module Bool where
  open import Data.Bool public using (Bool; true; false)

  bool : tp pos
  bool = U (meta Bool)

open Bool

record Comparable : Set₁ where
  field
    A : tp pos
    _≤_ : val A → val A → Set
    _≤ᵇ_ : val A → val A → cmp (F bool)
    ≤ᵇ-reflects-≤ : ∀ {x y b} → ◯ ((x ≤ᵇ y) ≡ ret b → Reflects (x ≤ y) b)
    ≤-refl : Reflexive _≤_
    ≤-trans : Transitive _≤_
    ≤-total : Total _≤_
    ≤-antisym : Antisymmetric _≡_ _≤_
    h-cost : (x y : val A) → ub bool (x ≤ᵇ y) 1

NatComparable : Comparable
NatComparable = record
  { A = U (meta ℕ)
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step' (F bool) 1 (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = reflects
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ → ub/step/suc 0 (ub/ret 0)
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {m n b} → ◯ (step' (F bool) 1 (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step'/ext (F bool) (ret (m ≤ᵇ n)) 1 u) h)
    ... | refl = ≤ᵇ-reflects-≤ m n

module Core (M : Comparable) where
  open Comparable M

  open import Data.List.Relation.Binary.Permutation.Propositional public
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties public
  open import Data.List.Relation.Unary.All public
  open import Data.List.Relation.Unary.Any using (Any; here; there)

  _≤*_ : val A → val (list A) → Set
  _≤*_ x = All (x ≤_)

  ≤-≤* : ∀ {x₁ x₂ l} → x₁ ≤ x₂ → x₂ ≤* l → x₁ ≤* l
  ≤-≤* x₁≤x₂ = map (≤-trans x₁≤x₂)

  All-++ : {P : val A → Set} {l₁ l₂ : val (list A)} → All P l₁ → All P l₂ → All P (l₁ ++ l₂)
  All-++ []        a₂ = a₂
  All-++ (px ∷ a₁) a₂ = px ∷ All-++ a₁ a₂

  ↭-All : {P : val A → Set} {l l' : val (list A)} → l ↭ l' → All P l → All P l'
  ↭-All refl h = h
  ↭-All (prep x p) (px ∷ h) = px ∷ ↭-All p h
  ↭-All (swap x₁ x₂ p) (px₁ ∷ px₂ ∷ h) = px₂ ∷ px₁ ∷ ↭-All p h
  ↭-All (trans p₁ p₂) h = ↭-All p₂ (↭-All p₁ h)

  ↭-Any : {P : val A → Set} {l l' : val (list A)} → l ↭ l' → Any P l → Any P l'
  ↭-Any refl h = h
  ↭-Any (prep x ↭) (here px) = here px
  ↭-Any (prep x ↭) (there h) = there (↭-Any (↭) h)
  ↭-Any (swap x y ↭) (here px) = there (here px)
  ↭-Any (swap x y ↭) (there (here py)) = here py
  ↭-Any (swap x y ↭) (there (there h)) = there (there (↭-Any (↭) h))
  ↭-Any (trans ↭₁ ↭₂) h = ↭-Any ↭₂ (↭-Any ↭₁ h)

  data Sorted : val (list A) → Set where
    [] : Sorted []
    _∷_ : ∀ {y ys} → y ≤* ys → Sorted ys → Sorted (y ∷ ys)

  short-sorted : {l : val (list A)} → length l Nat.≤ 1 → Sorted l
  short-sorted {[]} _ = []
  short-sorted {_ ∷ []} _ = [] ∷ []
  short-sorted {_ ∷ _ ∷ _} (s≤s ())

  unique-sorted : ∀ {l'₁ l'₂} → Sorted l'₁ → Sorted l'₂ → l'₁ ↭ l'₂ → l'₁ ≡ l'₂
  unique-sorted []             []             ↭ = refl
  unique-sorted []             (h₂ ∷ sorted₂) ↭ = ⊥-elim (¬x∷xs↭[] (↭-sym ↭))
  unique-sorted (h₁ ∷ sorted₁) []             ↭ = ⊥-elim (¬x∷xs↭[] ↭)
  unique-sorted (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) ↭ with
    ≤-antisym
      (lookup (≤-refl ∷ h₁) (↭-Any (↭-sym ↭) (here refl)))
      (lookup (≤-refl ∷ h₂) (↭-Any (↭) (here refl)))
  ... | refl = Eq.cong (_ ∷_) (unique-sorted sorted₁ sorted₂ (drop-∷ ↭))

  SortedOf : val (list A) → val (list A) → Set
  SortedOf l l' = l ↭ l' × Sorted l'

  SortResult : cmp (Π (list A) λ _ → F (list A)) → val (list A) → Set
  SortResult sort l = ◯ (∃ λ l' → sort l ≡ ret l' × SortedOf l l')

  IsSort : cmp (Π (list A) λ _ → F (list A)) → Set
  IsSort sort = ∀ l → SortResult sort l

cost = meta ℕ

test/forward  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ []
test/backward = 16 ∷ 15 ∷ 14 ∷ 13 ∷ 12 ∷ 11 ∷ 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
test/shuffled = 4 ∷ 8 ∷ 12 ∷ 16 ∷ 13 ∷ 3 ∷ 5 ∷ 14 ∷ 9 ∷ 6 ∷ 7 ∷ 10 ∷ 11 ∷ 1 ∷ 2 ∷ 15 ∷ []

module InsertionSort (M : Comparable) where
  open Comparable M
  open Core M

  insert : cmp (Π A λ _ → Π (list A) λ _ → F (list A))
  insert x []       = ret [ x ]
  insert x (y ∷ ys) =
    bind (F (list A)) (x ≤ᵇ y)
      λ { false → bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))
        ; true  → ret (x ∷ (y ∷ ys)) }

  insert/correct : ∀ x l → Sorted l → ◯ (∃ λ l' → insert x l ≡ ret l' × SortedOf (x ∷ l) l')
  insert/correct x []       []       u = [ x ] , refl , refl , [] ∷ []
  insert/correct x (y ∷ ys) (h ∷ hs) u with h-cost x y
  insert/correct x (y ∷ ys) (h ∷ hs) u | ub/intro {q = q} b _ h-eq rewrite eq/ref h-eq
    with ≤ᵇ-reflects-≤ u (Eq.trans (eq/ref h-eq) (step'/ext (F bool) (ret b) q u)) | ≤-total x y
  insert/correct x (y ∷ ys) (h ∷ hs) u | ub/intro {q = q} false _ _ | ofⁿ ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
  insert/correct x (y ∷ ys) (h ∷ hs) u | ub/intro {q = q} false _ _ | ofⁿ ¬x≤y | inj₂ x≤y =
    let (ys' , h-ys' , x∷ys↭ys' , sorted-ys') = insert/correct x ys hs u in
    y ∷ ys' , (
      let open ≡-Reasoning in
      begin
        step' (F (list A)) q (bind (F (list A)) (insert x ys) (ret ∘ (y ∷_)))
      ≡⟨ step'/ext (F (list A)) (bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))) q u ⟩
        bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e (ret ∘ (y ∷_))) h-ys' ⟩
        ret (y ∷ ys')
      ∎
    ) , (
      let open PermutationReasoning in
      begin
        x ∷ y ∷ ys
      <<⟨ refl ⟩
        y ∷ (x ∷ ys)
      <⟨ x∷ys↭ys' ⟩
        y ∷ ys'
      ∎
    ) , ↭-All x∷ys↭ys' (x≤y ∷ h) ∷ sorted-ys'
  insert/correct x (y ∷ ys) (h ∷ hs) u | ub/intro {q = q} true _ _ | ofʸ x≤y | _ =
    x ∷ (y ∷ ys) , step'/ext (F (list A)) (ret _) q u , refl , (x≤y ∷ ≤-≤* x≤y h) ∷ (h ∷ hs)

  insert/length : ∀ x l (κ : ℕ → α) → bind (meta α) (insert x l) (κ ∘ length) ≡ κ (suc (length l))
  insert/length x []       κ = refl
  insert/length x (y ∷ ys) κ with h-cost x y
  ... | ub/intro false _ h-eq rewrite eq/ref h-eq = insert/length x ys (κ ∘ suc)
  ... | ub/intro true  _ h-eq rewrite eq/ref h-eq = refl

  insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost _ = length

  insert≤insert/cost : ∀ x l → ub (list A) (insert x l) (insert/cost x l)
  insert≤insert/cost x []       = ub/ret zero
  insert≤insert/cost x (y ∷ ys) with h-cost x y
  ... | ub/intro true  q≤1 h-eq rewrite eq/ref h-eq =
    ub/intro _ (N.≤-trans q≤1 (s≤s z≤n)) (ret (eq/intro refl))
  ... | ub/intro {q = q} false q≤1 h-eq rewrite eq/ref h-eq =
    ub/relax
      (begin
        length ys + q + 0
      ≡⟨ N.+-identityʳ _ ⟩
        length ys + q
      ≡⟨ N.+-comm (length ys) q ⟩
        q + length ys
      ≤⟨ N.+-monoˡ-≤ _ q≤1 ⟩
        suc (length ys)
      ∎)
      (ub/bind/const _ _ (ub/step (length ys) q (insert≤insert/cost x ys)) λ _ → ub/ret zero)
      where open ≤-Reasoning

  sort : cmp (Π (list A) λ _ → F (list A))
  sort []       = ret []
  sort (x ∷ xs) = bind (F (list A)) (sort xs) (insert x)

  sort/correct : IsSort sort
  sort/correct []       u = [] , refl , refl , []
  sort/correct (x ∷ xs) u =
    let (xs'   , h-xs'   , xs↭xs'     , sorted-xs'  ) = sort/correct xs u in
    let (x∷xs' , h-x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') = insert/correct x xs' sorted-xs' u in
    x∷xs' , (
      let open ≡-Reasoning in
      begin
        sort (x ∷ xs)
      ≡⟨⟩
        bind (F (list A)) (sort xs) (insert x)
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e (insert x)) h-xs' ⟩
        bind (F (list A)) (ret {list A} xs') (insert x)
      ≡⟨⟩
        insert x xs'
      ≡⟨ h-x∷xs' ⟩
        ret x∷xs'
      ∎
    ) , (
      let open PermutationReasoning in
      begin
        x ∷ xs
      <⟨ xs↭xs' ⟩
        x ∷ xs'
      ↭⟨ x∷xs↭x∷xs' ⟩
        x∷xs'
      ∎
    ) , sorted-x∷xs'

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

  sort≤n² : ∀ l → ub (list A) (sort l) (length l ^ 2)
  sort≤n² l = ub/relax (sort/cost≤n² l) (sort≤sort/cost l)
    where
      sort/cost≤n² : ∀ l → sort/cost l Nat.≤ (length l ^ 2)
      sort/cost≤n² []       = z≤n
      sort/cost≤n² (x ∷ xs) =
        begin
          sort/cost (x ∷ xs)
        ≡⟨⟩
          sort/cost xs + length xs
        ≤⟨ N.+-monoˡ-≤ (length xs) (sort/cost≤n² xs) ⟩
          length xs ^ 2 + length xs
        ≡⟨ N.+-comm (length xs ^ 2) (length xs) ⟩
          length xs + length xs ^ 2
        ≡⟨ Eq.cong (λ n → length xs + length xs * n) (N.*-identityʳ (length xs)) ⟩
          length xs + length xs * length xs
        ≤⟨ N.m≤n+m (length xs + length xs * length xs) (suc (length xs)) ⟩
          suc (length xs) + (length xs + length xs * length xs)
        ≡⟨⟩
          suc (length xs + (length xs + length xs * length xs))
        ≡˘⟨ Eq.cong (λ n → suc (length xs + n)) (N.*-suc (length xs) (length xs)) ⟩
          suc (length xs + length xs * suc (length xs))
        ≡˘⟨ Eq.cong (λ n → suc (n + length xs * suc n)) (N.*-identityʳ (length xs)) ⟩
          suc (length xs * 1 + length xs * suc (length xs * 1))
        ≡⟨⟩
          length (x ∷ xs) ^ 2
        ∎
          where open ≤-Reasoning

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
  open Core M

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ {x} {y} h with ≤-total x y
  ... | inj₁ h₁ = ⊥-elim (h h₁)
  ... | inj₂ h₂ = h₂

  module _ where

    ⌈log₂⌉/aux : (n : ℕ) → (m : ℕ) → m Nat.≤ n → ℕ
    ⌈log₂⌉/aux _ zero _ = zero
    ⌈log₂⌉/aux _ (suc zero) _ = zero
    ⌈log₂⌉/aux (suc (suc n)) (suc (suc m)) (s≤s (s≤s h-strong)) =
      suc (⌈log₂⌉/aux (suc n) (⌈ suc (suc m) /2⌉) (s≤s (N.≤-trans (N.⌈n/2⌉≤n m) h-strong)))

    ⌈log₂⌉/aux-unique : {m n₁ n₂ : ℕ} → {h₁ : m Nat.≤ n₁} → {h₂ : m Nat.≤ n₂} →
      ⌈log₂⌉/aux n₁ m h₁ ≡ ⌈log₂⌉/aux n₂ m h₂
    ⌈log₂⌉/aux-unique {zero} = refl
    ⌈log₂⌉/aux-unique {suc zero} = refl
    ⌈log₂⌉/aux-unique {suc (suc m)} {h₁ = s≤s (s≤s _)} {h₂ = s≤s (s≤s _)} = Eq.cong suc ⌈log₂⌉/aux-unique

    ⌈log₂_⌉ : ℕ → ℕ
    ⌈log₂ n ⌉ = ⌈log₂⌉/aux n n N.≤-refl

    log₂-mono : ⌈log₂_⌉ Preserves Nat._≤_ ⟶ Nat._≤_
    log₂-mono {m₁} {m₂} h =
      begin
        ⌈log₂ m₁ ⌉
      ≡⟨ ⌈log₂⌉/aux-unique ⟩
        ⌈log₂⌉/aux m₂ m₁ h
      ≤⟨ ⌈log₂⌉/aux-mono h ⟩
        ⌈log₂ m₂ ⌉
      ∎
        where
          open ≤-Reasoning

          ⌈log₂⌉/aux-mono : {m₁ m₂ n : ℕ} → {h₁ : m₁ Nat.≤ n} → {h₂ : m₂ Nat.≤ n} →
            m₁ Nat.≤ m₂ → ⌈log₂⌉/aux n m₁ h₁ Nat.≤ ⌈log₂⌉/aux n m₂ h₂
          ⌈log₂⌉/aux-mono {zero} _ = z≤n
          ⌈log₂⌉/aux-mono {suc zero} _ = z≤n
          ⌈log₂⌉/aux-mono {suc (suc _)} {h₁ = s≤s (s≤s _)} {h₂ = s≤s (s≤s _)} (s≤s (s≤s h)) =
            s≤s (⌈log₂⌉/aux-mono (N.⌈n/2⌉-mono (s≤s (s≤s h))))

    log₂-suc : ∀ {n k} → ⌈log₂ n ⌉ Nat.≤ suc k → ⌈log₂ ⌈ n /2⌉ ⌉ Nat.≤ k
    log₂-suc {zero} h = z≤n
    log₂-suc {suc zero} h = z≤n
    log₂-suc {suc (suc n)} {k} (s≤s h) =
      begin
        ⌈log₂ ⌈ suc (suc n) /2⌉ ⌉
      ≡⟨ ⌈log₂⌉/aux-unique ⟩
        ⌈log₂⌉/aux (suc n) ⌈ suc (suc n) /2⌉ _
      ≤⟨ h ⟩
        k
      ∎
        where open ≤-Reasoning

    ⌈log₂n⌉≡0⇒n≤1 : {n : ℕ} → ⌈log₂ n ⌉ ≡ 0 → n Nat.≤ 1
    ⌈log₂n⌉≡0⇒n≤1 {zero} refl = z≤n
    ⌈log₂n⌉≡0⇒n≤1 {suc zero} refl = s≤s z≤n

  pair = Σ++ (list A) λ _ → (list A)

  split/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → F pair)
  split/clocked zero    l        = ret ([] , l)
  split/clocked (suc k) []       = ret ([] , [])
  split/clocked (suc k) (x ∷ xs) = bind (F pair) (split/clocked k xs) λ (l₁ , l₂) → ret (x ∷ l₁ , l₂)

  split/clocked/correct : ∀ k k' l → k + k' ≡ length l →
    ◯ (∃ λ l₁ → ∃ λ l₂ → split/clocked k l ≡ ret (l₁ , l₂) × length l₁ ≡ k × length l₂ ≡ k' × l ↭ (l₁ ++ l₂))
  split/clocked/correct zero    k' l        refl u = [] , l , refl , refl , refl , refl
  split/clocked/correct (suc k) k' (x ∷ xs) h    u =
    let (l₁ , l₂ , ≡ , h₁ , h₂ , ↭) = split/clocked/correct k k' xs (N.suc-injective h) u in
    x ∷ l₁ , l₂ , Eq.cong (λ e → bind (F pair) e _) ≡ , Eq.cong suc h₁ , h₂ , prep x ↭

  split/clocked/length : ∀ k k' l → k + k' ≡ length l → (κ : ℕ → ℕ → α) →
    bind (meta α) (split/clocked k l) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ k k'
  split/clocked/length zero    _  l        refl _ = refl
  split/clocked/length (suc k) k' (x ∷ xs) h    κ = split/clocked/length k k' xs (N.suc-injective h) (κ ∘ suc)

  split/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  split/clocked/cost _ _ = zero

  split/clocked≤split/clocked/cost : ∀ k l → ub pair (split/clocked k l) (split/clocked/cost k l)
  split/clocked≤split/clocked/cost zero    l        = ub/ret _
  split/clocked≤split/clocked/cost (suc k) []       = ub/ret _
  split/clocked≤split/clocked/cost (suc k) (x ∷ xs) = ub/bind/const zero zero (split/clocked≤split/clocked/cost k xs) λ _ → ub/ret _

  split : cmp (Π (list A) λ _ → F pair)
  split l = split/clocked ⌊ length l /2⌋ l

  split/correct : ∀ l →
    ◯ (∃ λ l₁ → ∃ λ l₂ → split l ≡ ret (l₁ , l₂) × length l₁ ≡ ⌊ length l /2⌋ × length l₂ ≡ ⌈ length l /2⌉ × l ↭ (l₁ ++ l₂))
  split/correct l = split/clocked/correct ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

  split/length : ∀ l (κ : ℕ → ℕ → α) →
    bind (meta α) (split l) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ ⌊ length l /2⌋ ⌈ length l /2⌉
  split/length l = split/clocked/length ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

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
      λ { false → bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_))
        ; true  → bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_)) }

  merge/clocked/correct : ∀ k l₁ l₂ → length l₁ + length l₂ Nat.≤ k → Sorted l₁ → Sorted l₂ →
    ◯ (∃ λ l → merge/clocked k (l₁ , l₂) ≡ ret l × SortedOf (l₁ ++ l₂) l)
  merge/clocked/correct zero    []       []       h       sorted₁        sorted₂        u =
    [] , refl , refl , []
  merge/clocked/correct (suc k) []       l₂       h       sorted₁        sorted₂        u =
    l₂ , refl , refl , sorted₂
  merge/clocked/correct (suc k) (x ∷ xs) []       h       sorted₁        sorted₂        u
    rewrite List.++-identityʳ (x ∷ xs) = x ∷ xs , refl , refl , sorted₁
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) (s≤s h) (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) u with h-cost x y
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) (s≤s h) (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) u | ub/intro {q = q} b _ h-eq rewrite eq/ref h-eq
    with ≤ᵇ-reflects-≤ u (Eq.trans (eq/ref h-eq) (step'/ext (F bool) (ret b) q u))
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) (s≤s h) (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) u | ub/intro {q = q} false _ h-eq | ofⁿ ¬p =
    let h = Eq.subst (Nat._≤ k) (N.+-suc (length xs) (length ys)) h in
    let (l , ≡ , ↭ , sorted) = merge/clocked/correct k (x ∷ xs) ys h (h₁ ∷ sorted₁) sorted₂ u in
    let p = ≰⇒≥ ¬p in
    y ∷ l , (
      let open ≡-Reasoning in
      begin
        step' (F (list A)) q (bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_)))
      ≡⟨ step'/ext (F (list A)) (bind (F (list A)) (merge/clocked k _) _) q u ⟩
        bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        ret (y ∷ l)
      ∎
    ) , (
      let open PermutationReasoning in
      begin
        (x ∷ xs ++ y ∷ ys)
      ↭⟨ ++-comm (x ∷ xs) (y ∷ ys) ⟩
        (y ∷ ys ++ x ∷ xs)
      ≡⟨⟩
        y ∷ (ys ++ x ∷ xs)
      <⟨ ++-comm ys (x ∷ xs) ⟩
        y ∷ (x ∷ xs ++ ys)
      <⟨ ↭ ⟩
        y ∷ l
      ∎
     ) , ↭-All (↭) (All-++ (p ∷ ≤-≤* p h₁) h₂) ∷ sorted
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) (s≤s h) (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) u | ub/intro {q = q} true  _ h-eq | ofʸ p =
    let (l , ≡ , ↭ , sorted) = merge/clocked/correct k xs (y ∷ ys) h sorted₁ (h₂ ∷ sorted₂) u in
    x ∷ l , (
      let open ≡-Reasoning in
      begin
        step' (F (list A)) q (bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_)))
      ≡⟨ step'/ext (F (list A)) (bind (F (list A)) (merge/clocked k _) _) q u ⟩
        bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        ret (x ∷ l)
      ∎
    ) , prep x ↭ , ↭-All (↭) (All-++ h₁ (p ∷ ≤-≤* p h₂)) ∷ sorted

  merge/clocked/length : ∀ k (l₁ l₂ : val (list A)) (κ : ℕ → α) →
    bind (meta α) (merge/clocked k (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  merge/clocked/length zero    l₁       l₂       κ = Eq.cong κ (length-++ l₁)
  merge/clocked/length (suc k) []       l₂       κ = refl
  merge/clocked/length (suc k) (x ∷ xs) []       κ = Eq.cong (κ ∘ suc) (Eq.sym (N.+-identityʳ (length xs)))
  merge/clocked/length (suc k) (x ∷ xs) (y ∷ ys) κ with h-cost x y
  ... | ub/intro false _ h-eq rewrite eq/ref h-eq =
    begin
      bind _ (merge/clocked k (x ∷ xs , ys)) (λ l → (κ ∘ length) (y ∷ l))
    ≡⟨⟩
      bind _ (merge/clocked k (x ∷ xs , ys)) (λ l → (κ ∘ suc) (length l))
    ≡⟨ merge/clocked/length k (x ∷ xs) ys (κ ∘ suc) ⟩
      κ (suc (length (x ∷ xs) + length ys))
    ≡˘⟨ Eq.cong κ (N.+-suc (length (x ∷ xs)) (length ys)) ⟩
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
    ub/bind/const 1 k (h-cost x y)
      λ { false → ub/bind/const' k zero (N.+-identityʳ k) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret _
        ; true  → ub/bind/const' k zero (N.+-identityʳ k) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret _ }

  merge : cmp (Π pair λ _ → F (list A))
  merge (l₁ , l₂) = merge/clocked (length l₁ + length l₂) (l₁ , l₂)

  merge/correct : ∀ l₁ l₂ → Sorted l₁ → Sorted l₂ →
    ◯ (∃ λ l → merge (l₁ , l₂) ≡ ret l × SortedOf (l₁ ++ l₂) l)
  merge/correct l₁ l₂ = merge/clocked/correct (length l₁ + length l₂) l₁ l₂ N.≤-refl

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

  sort/clocked/correct : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → SortResult (sort/clocked k) l
  sort/clocked/correct zero    l h u = l , refl , refl , short-sorted (⌈log₂n⌉≡0⇒n≤1 (N.n≤0⇒n≡0 h))
  sort/clocked/correct (suc k) l h u =
    let (l₁ , l₂ , ≡ , length₁ , length₂ , ↭) = split/correct l u in
    let (l₁' , ≡₁ , ↭₁ , sorted₁) = sort/clocked/correct k l₁ (
                                      let open ≤-Reasoning in
                                      begin
                                        ⌈log₂ length l₁ ⌉
                                      ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
                                        ⌈log₂ ⌊ length l /2⌋ ⌉
                                      ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
                                        ⌈log₂ ⌈ length l /2⌉ ⌉
                                      ≤⟨ log₂-suc h ⟩
                                        k
                                      ∎
                                    ) u in
    let (l₂' , ≡₂ , ↭₂ , sorted₂) = sort/clocked/correct k l₂ (
                                      let open ≤-Reasoning in
                                      begin
                                        ⌈log₂ length l₂ ⌉
                                      ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
                                        ⌈log₂ ⌈ length l /2⌉ ⌉
                                      ≤⟨ log₂-suc h ⟩
                                        k
                                      ∎
                                    ) u in
    let (l' , ≡' , ↭' , sorted) = merge/correct l₁' l₂' sorted₁ sorted₂ u in
    l' , (
      let open ≡-Reasoning in
      begin
        sort/clocked (suc k) l
      ≡⟨⟩
        (bind (F (list A)) (split l) λ (l₁ , l₂) →
          bind (F (list A)) (sort/clocked k l₁) λ l₁' →
            bind (F (list A)) (sort/clocked k l₂) λ l₂' →
              merge (l₁' , l₂'))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        (bind (F (list A)) (sort/clocked k l₁) λ l₁' →
          bind (F (list A)) (sort/clocked k l₂) λ l₂' →
            merge (l₁' , l₂'))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e λ l₁' → bind (F (list A)) (sort/clocked k l₂) _) ≡₁ ⟩
        (bind (F (list A)) (sort/clocked k l₂) λ l₂' →
          merge (l₁' , l₂'))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e λ l₂' → merge (l₁' , l₂')) ≡₂ ⟩
        merge (l₁' , l₂')
      ≡⟨ ≡' ⟩
        ret l'
      ∎
    ) , (
      let open PermutationReasoning in
      begin
        l
      ↭⟨ ↭ ⟩
        l₁ ++ l₂
      ↭⟨ ++⁺ ↭₁ ↭₂ ⟩
        l₁' ++ l₂'
      ↭⟨ ↭' ⟩
        l'
      ∎
    ) , sorted

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
    ≡⟨ Eq.cong κ (N.⌊n/2⌋+⌈n/2⌉≡n (length l)) ⟩
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
    Eq.subst (ub _ _) (Eq.sym (N.+-assoc (sort/recurrence k ⌊ length l /2⌋) _ _)) (
      Eq.subst (ub _ _) (Eq.cong (λ n → sort/recurrence k ⌊ length l /2⌋ + (sort/recurrence k ⌈ length l /2⌉ + n)) (N.⌊n/2⌋+⌈n/2⌉≡n _)) (
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
  sort/depth l = ⌈log₂ length l ⌉

  sort/clocked≤nlog₂n : ∀ l → ub (list A) (sort/clocked (sort/depth l) l) (length l * ⌈log₂ length l ⌉)
  sort/clocked≤nlog₂n l = Eq.subst (ub (list A) _) (sort/recurrence≡* _ (length l)) (sort/clocked≤sort/clocked/cost _ l)
    where
      open ≡-Reasoning

      lemma0 : ∀ k → sort/recurrence k zero ≡ zero
      lemma0 zero    = refl
      lemma0 (suc k) = Eq.cong (_+ zero) (Eq.cong₂ _+_ (lemma0 k) (lemma0 k))

      lemma1 : ∀ k → sort/recurrence k 1 ≡ k
      lemma1 zero    = refl
      lemma1 (suc k) =
        begin
          sort/recurrence (suc k) 1
        ≡⟨⟩
          sort/recurrence k zero + sort/recurrence k ⌈ 1 /2⌉ + 1
        ≡⟨ Eq.cong (_+ 1) (Eq.cong (_+ sort/recurrence k ⌈ 1 /2⌉) (lemma0 k)) ⟩
          sort/recurrence k ⌈ 1 /2⌉ + 1
        ≡⟨⟩
          sort/recurrence k 1 + 1
        ≡⟨ N.+-comm _ 1 ⟩
          suc (sort/recurrence k 1)
        ≡⟨ Eq.cong suc (lemma1 k) ⟩
          suc k
        ∎

      sort/recurrence≡* : ∀ k n → sort/recurrence k n ≡ n * k
      sort/recurrence≡* k zero = lemma0 k
      sort/recurrence≡* k (suc zero) =
        begin
          sort/recurrence k (suc zero)
        ≡⟨ lemma1 k ⟩
          k
        ≡˘⟨ N.*-identityˡ k ⟩
          1 * k
        ∎
      sort/recurrence≡* zero (suc (suc n)) = Eq.sym (N.*-zeroʳ n)
      sort/recurrence≡* (suc k) (suc (suc n)) =
        begin
          sort/recurrence (suc k) (suc (suc n))
        ≡⟨⟩
          sort/recurrence k ⌊ suc (suc n) /2⌋ + sort/recurrence k ⌈ suc (suc n) /2⌉ + suc (suc n)
        ≡⟨
          Eq.cong (_+ suc (suc n)) (
            Eq.cong₂ _+_
              (sort/recurrence≡* k ⌊ suc (suc n) /2⌋)
              (sort/recurrence≡* k ⌈ suc (suc n) /2⌉)
          )
        ⟩
          ⌊ suc (suc n) /2⌋ * k + ⌈ suc (suc n) /2⌉ * k + suc (suc n)
        ≡˘⟨ Eq.cong (_+ suc (suc n)) (N.*-distribʳ-+ k ⌊ suc (suc n) /2⌋ ⌈ suc (suc n) /2⌉) ⟩
          (⌊ suc (suc n) /2⌋ + ⌈ suc (suc n) /2⌉) * k + suc (suc n)
        ≡⟨ Eq.cong (λ ssn → ssn * k + suc (suc n)) (N.⌊n/2⌋+⌈n/2⌉≡n (suc (suc n))) ⟩
          suc (suc n) * k + suc (suc n)
        ≡⟨ N.+-comm (suc (suc n) * k) (suc (suc n)) ⟩
          suc (suc n) + suc (suc n) * k
        ≡˘⟨ Eq.cong (_+ suc (suc n) * k) (N.*-identityʳ (suc (suc n))) ⟩
          suc (suc n) * 1 + suc (suc n) * k
        ≡˘⟨ N.*-distribˡ-+ (suc (suc n)) 1 k ⟩
          suc (suc n) * (1 + k)
        ≡⟨⟩
          suc (suc n) * suc k
        ∎

  sort : cmp (Π (list A) λ _ → F (list A))
  sort l = sort/clocked (sort/depth l) l

  sort/correct : IsSort sort
  sort/correct l = sort/clocked/correct (sort/depth l) l N.≤-refl

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost l = sort/clocked/cost (sort/depth l) l

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

  sort≤nlog₂n : ∀ l → ub (list A) (sort l) (length l * ⌈log₂ length l ⌉)
  sort≤nlog₂n l = sort/clocked≤nlog₂n l

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
  open Core M

  module ISort = InsertionSort M
  module MSort = MergeSort M

  isort≡msort : ◯ (ISort.sort ≡ MSort.sort)
  isort≡msort u =
    funext λ l →
      let (l'ᵢ , ≡ᵢ , ↭ᵢ , sortedᵢ) = ISort.sort/correct l u in
      let (l'ₘ , ≡ₘ , ↭ₘ , sortedₘ) = MSort.sort/correct l u in
      begin
        ISort.sort l
      ≡⟨ ≡ᵢ ⟩
        ret l'ᵢ
      ≡⟨ Eq.cong ret (unique-sorted sortedᵢ sortedₘ (trans (↭-sym ↭ᵢ) ↭ₘ)) ⟩
        ret l'ₘ
      ≡˘⟨ ≡ₘ ⟩
        MSort.sort l
      ∎
        where open ≡-Reasoning
