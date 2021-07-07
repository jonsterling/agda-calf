{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Sequential where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid

open CostMonoid costMonoid
  hiding (zero; _+_; _≤_; ≤-refl; ≤-trans)

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as N

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
    h-cost : (x y : val A) → IsBounded bool (x ≤ᵇ y) 1

NatComparable : Comparable
NatComparable = record
  { A = nat
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step (F bool) 1 (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = reflects
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ → bound/step 1 0 bound/ret
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {m n b} → ◯ (step (F bool) 1 (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step/ext (F bool) (ret (m ≤ᵇ n)) 1 u) h)
    ... | refl = ≤ᵇ-reflects-≤ m n

module Core (M : Comparable) where
  open Comparable M

  open import Data.List.Relation.Binary.Permutation.Propositional public
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties renaming (++⁺ to ++⁺-↭) public
  open import Data.List.Relation.Unary.All public
  open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺-All) public
  open import Data.List.Relation.Unary.Any using (Any; here; there)

  _≤*_ : val A → val (list A) → Set
  _≤*_ x = All (x ≤_)

  ≤-≤* : ∀ {x₁ x₂ l} → x₁ ≤ x₂ → x₂ ≤* l → x₁ ≤* l
  ≤-≤* x₁≤x₂ = map (≤-trans x₁≤x₂)

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
      (lookup (≤-refl ∷ h₁) (Any-resp-↭ (↭-sym ↭) (here refl)))
      (lookup (≤-refl ∷ h₂) (Any-resp-↭ (↭) (here refl)))
  ... | refl = Eq.cong (_ ∷_) (unique-sorted sorted₁ sorted₂ (drop-∷ ↭))

  SortedOf : val (list A) → val (list A) → Set
  SortedOf l l' = l ↭ l' × Sorted l'

  SortResult : cmp (Π (list A) λ _ → F (list A)) → val (list A) → Set
  SortResult sort l = ◯ (∃ λ l' → sort l ≡ ret l' × SortedOf l l')

  IsSort : cmp (Π (list A) λ _ → F (list A)) → Set
  IsSort sort = ∀ l → SortResult sort l

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
  insert/correct x (y ∷ ys) (h ∷ hs) u | ⇓ b withCost q [ _ , h-eq ] rewrite eq/ref h-eq
    with ≤ᵇ-reflects-≤ u (Eq.trans (eq/ref h-eq) (step/ext (F bool) (ret b) q u)) | ≤-total x y
  insert/correct x (y ∷ ys) (h ∷ hs) u | ⇓ false withCost q [ _ , _ ] | ofⁿ ¬x≤y | inj₁ x≤y = ⊥-elim (¬x≤y x≤y)
  insert/correct x (y ∷ ys) (h ∷ hs) u | ⇓ false withCost q [ _ , _ ] | ofⁿ ¬x≤y | inj₂ x≤y =
    let (ys' , h-ys' , x∷ys↭ys' , sorted-ys') = insert/correct x ys hs u in
    y ∷ ys' , (
      let open ≡-Reasoning in
      begin
        step (F (list A)) q (bind (F (list A)) (insert x ys) (ret ∘ (y ∷_)))
      ≡⟨ step/ext (F (list A)) (bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))) q u ⟩
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
    ) , All-resp-↭ x∷ys↭ys' (x≤y ∷ h) ∷ sorted-ys'
  insert/correct x (y ∷ ys) (h ∷ hs) u | ⇓ true withCost q [ _ , _ ] | ofʸ x≤y | _ =
    x ∷ (y ∷ ys) , step/ext (F (list A)) (ret _) q u , refl , (x≤y ∷ ≤-≤* x≤y h) ∷ (h ∷ hs)

  insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost x []       = zero
  insert/cost x (y ∷ ys) with h-cost x y
  ... | ⇓ false withCost q [ q≤1 , h-eq ] = q + (insert/cost x ys + zero)
  ... | ⇓ true  withCost q [ q≤1 , h-eq ] = q + 0

  insert/cost/closed : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost/closed x l = length l

  insert/cost≤insert/cost/closed : ∀ x l → ◯ (insert/cost x l Nat.≤ insert/cost/closed x l)
  insert/cost≤insert/cost/closed x []       u = N.≤-refl
  insert/cost≤insert/cost/closed x (y ∷ ys) u with h-cost x y
  ... | ⇓ false withCost q [ q≤1 , h-eq ] =
    Eq.subst (λ n → (q + n) Nat.≤ (suc (length ys))) (Eq.sym (+-identityʳ (insert/cost x ys))) (
      N.≤-trans
        (+-monoˡ-≤ _ (q≤1 u))
        (s≤s (insert/cost≤insert/cost/closed x ys u))
    )
  ... | ⇓ true  withCost q [ q≤1 , h-eq ] =
    Eq.subst (Nat._≤ (suc (length ys))) (Eq.sym (+-identityʳ q)) (
      N.≤-trans (q≤1 u) (s≤s z≤n)
    )

  insert≤insert/cost : ∀ x l → IsBounded (list A) (insert x l) (insert/cost x l)
  insert≤insert/cost x []       = bound/ret
  insert≤insert/cost x (y ∷ ys) with h-cost x y
  ... | ⇓ false withCost q [ q≤1 , h-eq ] rewrite eq/ref h-eq =
    bound/step q (insert/cost x ys + 0) (bound/bind/const (insert/cost x ys) 0 (insert≤insert/cost x ys) λ _ → bound/ret)
  ... | ⇓ true  withCost q [ q≤1 , h-eq ] rewrite eq/ref h-eq =
    bound/step q 0 bound/ret

  insert≤insert/cost/closed : ∀ x l → IsBounded (list A) (insert x l) (insert/cost/closed x l)
  insert≤insert/cost/closed x l = bound/relax (insert/cost≤insert/cost/closed x l) (insert≤insert/cost x l)

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

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost []       = 0
  sort/cost (x ∷ xs) = bind cost (sort xs) (λ xs' → sort/cost xs + insert/cost/closed x xs')

  sort/cost/closed : cmp (Π (list A) λ _ → cost)
  sort/cost/closed l = length l ^ 2

  sort/cost≤sort/cost/closed : ∀ l → ◯ (sort/cost l Nat.≤ sort/cost/closed l)
  sort/cost≤sort/cost/closed []       u = N.≤-refl
  sort/cost≤sort/cost/closed (x ∷ xs) u =
    let (xs' , ≡ , ↭ , sorted) = sort/correct xs u in
    begin
      sort/cost (x ∷ xs)
    ≡⟨⟩
      bind cost (sort xs) (λ xs' → sort/cost xs + length xs')
    ≡⟨ Eq.cong (λ e → bind cost e λ xs' → sort/cost xs + length xs') (≡) ⟩
      sort/cost xs + length xs'
    ≡˘⟨ Eq.cong (sort/cost xs +_) (↭-length ↭) ⟩
      sort/cost xs + length xs
    ≤⟨ +-monoˡ-≤ (insert/cost/closed x xs) (sort/cost≤sort/cost/closed xs u) ⟩
      sort/cost/closed xs + insert/cost/closed x xs
    ≡⟨⟩
      length xs ^ 2 + length xs
    ≤⟨ lemma/arithmetic (length xs) ⟩
      length (x ∷ xs) ^ 2
    ≡⟨⟩
      sort/cost/closed (x ∷ xs)
    ∎
      where
        open ≤-Reasoning

        lemma/arithmetic : ∀ n → n ^ 2 + n Nat.≤ suc n ^ 2
        lemma/arithmetic n =
          begin
            n ^ 2 + n
          ≡⟨ N.+-comm (n ^ 2) n ⟩
            n + n ^ 2
          ≡⟨ Eq.cong (λ m → n + n * m) (N.*-identityʳ n) ⟩
            n + n * n
          ≤⟨ N.m≤n+m (n + n * n) (suc n) ⟩
            suc n + (n + n * n)
          ≡⟨⟩
            suc (n + (n + n * n))
          ≡˘⟨ Eq.cong (λ m → suc (n + m)) (N.*-suc n n) ⟩
            suc (n + n * suc n)
          ≡˘⟨ Eq.cong (λ m → suc (m + n * suc m)) (N.*-identityʳ n) ⟩
            suc (n * 1 + n * suc (n * 1))
          ≡⟨⟩
            suc n ^ 2
          ∎

  sort≤sort/cost : ∀ l → IsBounded (list A) (sort l) (sort/cost l)
  sort≤sort/cost []       = bound/ret
  sort≤sort/cost (x ∷ xs) = bound/bind (sort/cost xs) (insert/cost/closed x) (sort≤sort/cost xs) (insert≤insert/cost/closed x)

  sort≤sort/cost/closed : ∀ l → IsBounded (list A) (sort l) (sort/cost/closed l)
  sort≤sort/cost/closed l = bound/relax (sort/cost≤sort/cost/closed l) (sort≤sort/cost l)

module Ex/InsertionSort where
  module Sort = InsertionSort NatComparable

  list' = list nat

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

    private
      aux : (P : ℕ → Set) → P zero → P (suc zero) → ((n : ℕ) → P ⌈ suc (suc n) /2⌉ → P (suc (suc n))) →
        (n : ℕ) → (m : ℕ) → m Nat.≤ n → P m
      aux P bc₀ bc₁ is n zero h = bc₀
      aux P bc₀ bc₁ is n (suc zero) h = bc₁
      aux P bc₀ bc₁ is (suc (suc n)) (suc (suc m)) (s≤s (s≤s h)) =
        is m (aux P bc₀ bc₁ is (suc n) ⌈ suc (suc m) /2⌉ (s≤s (N.≤-trans (N.⌈n/2⌉≤n m) h)))

    strong-induction : (P : ℕ → Set) → P zero → P (suc zero) → ((n : ℕ) → P ⌈ suc (suc n) /2⌉ → P (suc (suc n))) → (n : ℕ) → P n
    strong-induction P bc₀ bc₁ is n = aux P bc₀ bc₁ is n n N.≤-refl

    private
      strong-induction/is : ∀ {P bc₀ bc₁ is n} →
        aux P bc₀ bc₁ is (suc n) ⌈ suc (suc n) /2⌉ (s≤s (N.≤-trans (N.⌈n/2⌉≤n n) N.≤-refl)) ≡
        strong-induction P bc₀ bc₁ is ⌈ suc (suc n) /2⌉
      strong-induction/is {P} {bc₀} {bc₁} {is} {n} = aux/unique
        where
          aux/unique : ∀ {m n₁ n₂ h₁ h₂} → aux P bc₀ bc₁ is n₁ m h₁ ≡ aux P bc₀ bc₁ is n₂ m h₂
          aux/unique {zero} = refl
          aux/unique {suc zero} = refl
          aux/unique {suc (suc m)} {h₁ = s≤s (s≤s h₁)} {h₂ = s≤s (s≤s h₂)} = Eq.cong (is m) aux/unique
      {-# REWRITE strong-induction/is #-}

    ⌈log₂_⌉ : ℕ → ℕ
    ⌈log₂_⌉ = strong-induction (λ _ → ℕ) zero zero (λ _ → suc)

    log₂-mono : ⌈log₂_⌉ Preserves Nat._≤_ ⟶ Nat._≤_
    log₂-mono {n₁} {n₂} =
      strong-induction (λ n₁ → ∀ n₂ → n₁ Nat.≤ n₂ → ⌈log₂ n₁ ⌉ Nat.≤ ⌈log₂ n₂ ⌉)
        (λ _ _ → z≤n)
        (λ _ _ → z≤n)
        (λ { n₁ ih (suc (suc n₂)) (s≤s (s≤s h)) → s≤s (ih ⌈ suc (suc n₂) /2⌉ (N.⌈n/2⌉-mono (s≤s (s≤s h))))})
        n₁
        n₂

    log₂-suc : ∀ n {k} → ⌈log₂ n ⌉ Nat.≤ suc k → ⌈log₂ ⌈ n /2⌉ ⌉ Nat.≤ k
    log₂-suc zero h = z≤n
    log₂-suc (suc zero) h = z≤n
    log₂-suc (suc (suc n)) (s≤s h) = h

    ⌈log₂n⌉≡0⇒n≤1 : {n : ℕ} → ⌈log₂ n ⌉ ≡ 0 → n Nat.≤ 1
    ⌈log₂n⌉≡0⇒n≤1 {zero} refl = z≤n
    ⌈log₂n⌉≡0⇒n≤1 {suc zero} refl = s≤s z≤n

  pair = Σ++ (list A) λ _ → (list A)

  split/clocked : cmp (Π nat λ _ → Π (list A) λ _ → F pair)
  split/clocked zero    l        = ret ([] , l)
  split/clocked (suc k) []       = ret ([] , [])
  split/clocked (suc k) (x ∷ xs) = bind (F pair) (split/clocked k xs) λ (l₁ , l₂) → ret (x ∷ l₁ , l₂)

  split/clocked/correct : ∀ k k' l → k + k' ≡ length l →
    ◯ (∃ λ l₁ → ∃ λ l₂ → split/clocked k l ≡ ret (l₁ , l₂) × length l₁ ≡ k × length l₂ ≡ k' × l ↭ (l₁ ++ l₂))
  split/clocked/correct zero    k' l        refl u = [] , l , refl , refl , refl , refl
  split/clocked/correct (suc k) k' (x ∷ xs) h    u =
    let (l₁ , l₂ , ≡ , h₁ , h₂ , ↭) = split/clocked/correct k k' xs (N.suc-injective h) u in
    x ∷ l₁ , l₂ , Eq.cong (λ e → bind (F pair) e _) ≡ , Eq.cong suc h₁ , h₂ , prep x ↭

  split/clocked/cost : cmp (Π nat λ _ → Π (list A) λ _ → cost)
  split/clocked/cost _ _ = zero

  split/clocked≤split/clocked/cost : ∀ k l → IsBounded pair (split/clocked k l) (split/clocked/cost k l)
  split/clocked≤split/clocked/cost zero    l        = bound/ret
  split/clocked≤split/clocked/cost (suc k) []       = bound/ret
  split/clocked≤split/clocked/cost (suc k) (x ∷ xs) = bound/bind/const zero zero (split/clocked≤split/clocked/cost k xs) λ _ → bound/ret

  split : cmp (Π (list A) λ _ → F pair)
  split l = split/clocked ⌊ length l /2⌋ l

  split/correct : ∀ l →
    ◯ (∃ λ l₁ → ∃ λ l₂ → split l ≡ ret (l₁ , l₂) × length l₁ ≡ ⌊ length l /2⌋ × length l₂ ≡ ⌈ length l /2⌉ × l ↭ (l₁ ++ l₂))
  split/correct l = split/clocked/correct ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))

  split/cost : cmp (Π (list A) λ _ → cost)
  split/cost l = split/clocked/cost ⌊ length l /2⌋ l

  split≤split/cost : ∀ l → IsBounded pair (split l) (split/cost l)
  split≤split/cost l = split/clocked≤split/clocked/cost ⌊ length l /2⌋ l

  merge/clocked : cmp (Π nat λ _ → Π pair λ _ → F (list A))
  merge/clocked zero    (l₁     , l₂    ) = ret (l₁ ++ l₂)
  merge/clocked (suc k) ([]     , l₂    ) = ret l₂
  merge/clocked (suc k) (x ∷ xs , []    ) = ret (x ∷ xs)
  merge/clocked (suc k) (x ∷ xs , y ∷ ys) =
    bind (F (list A)) (x ≤ᵇ y) λ b →
      if b
        then (bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_)))
        else (bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_)))

  merge/clocked/correct : ∀ k l₁ l₂ →
    ◯ (∃ λ l → merge/clocked k (l₁ , l₂) ≡ ret l × (length l₁ + length l₂ Nat.≤ k → Sorted l₁ → Sorted l₂ → SortedOf (l₁ ++ l₂) l))
  merge/clocked/correct zero    l₁       l₂       u = l₁ ++ l₂ , refl , λ { h [] [] → refl , [] }
  merge/clocked/correct (suc k) []       l₂       u = l₂ , refl , λ { h [] sorted₂ → refl , sorted₂ }
  merge/clocked/correct (suc k) (x ∷ xs) []       u = x ∷ xs , refl , λ { h sorted₁ [] → ++-identityʳ (x ∷ xs) , sorted₁ }
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) u with h-cost x y
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) u | ⇓ b withCost q [ _ , h-eq ] rewrite eq/ref h-eq
    with ≤ᵇ-reflects-≤ u (Eq.trans (eq/ref h-eq) (step/ext (F bool) (ret b) q u))
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) u | ⇓ false withCost q [ _ , h-eq ] | ofⁿ ¬p =
    let (l , ≡ , h-sorted) = merge/clocked/correct k (x ∷ xs) ys u in
    y ∷ l , (
      let open ≡-Reasoning in
      begin
        step (F (list A)) q (bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_)))
      ≡⟨ step/ext (F (list A)) (bind (F (list A)) (merge/clocked k _) _) q u ⟩
        bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        ret (y ∷ l)
      ∎
    ) , (
      λ { (s≤s h) (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) →
        let h = Eq.subst (Nat._≤ k) (N.+-suc (length xs) (length ys)) h in
        let (↭ , sorted) = h-sorted h (h₁ ∷ sorted₁) sorted₂ in
        (
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
        ) , (
          let p = ≰⇒≥ ¬p in
          All-resp-↭ (↭) (++⁺-All (p ∷ ≤-≤* p h₁) h₂) ∷ sorted
        )
      }
    )
  merge/clocked/correct (suc k) (x ∷ xs) (y ∷ ys) u | ⇓ true withCost q [ _ , h-eq ] | ofʸ p =
    let (l , ≡ , h-sorted) = merge/clocked/correct k xs (y ∷ ys) u in
    x ∷ l , (
      let open ≡-Reasoning in
      begin
        step (F (list A)) q (bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_)))
      ≡⟨ step/ext (F (list A)) (bind (F (list A)) (merge/clocked k _) _) q u ⟩
        bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_))
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        ret (x ∷ l)
      ∎
    ) , (
      λ { (s≤s h) (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) →
        let (↭ , sorted) = h-sorted h sorted₁ (h₂ ∷ sorted₂)  in
        prep x ↭ , All-resp-↭ (↭) (++⁺-All h₁ (p ∷ ≤-≤* p h₂)) ∷ sorted
      }
    )

  merge/clocked/cost : cmp (Π nat λ _ → Π pair λ _ → cost)
  merge/clocked/cost zero    (l₁     , l₂    ) = zero
  merge/clocked/cost (suc k) ([]     , l₂    ) = zero
  merge/clocked/cost (suc k) (x ∷ xs , []    ) = zero
  merge/clocked/cost (suc k) (x ∷ xs , y ∷ ys) =
    bind cost (x ≤ᵇ y) λ b →
      1 + (
        if b
          then (bind cost (merge/clocked k (xs , y ∷ ys)) (λ l → merge/clocked/cost k (xs , y ∷ ys) + 0))
          else (bind cost (merge/clocked k (x ∷ xs , ys)) (λ l → merge/clocked/cost k (x ∷ xs , ys) + 0))
      )

  merge/clocked/cost/closed : cmp (Π nat λ _ → Π pair λ _ → cost)
  merge/clocked/cost/closed k _ = k

  merge/clocked/cost≤merge/clocked/cost/closed : ∀ k p → ◯ (merge/clocked/cost k p Nat.≤ merge/clocked/cost/closed k p)
  merge/clocked/cost≤merge/clocked/cost/closed zero    (l₁     , l₂    ) u = N.≤-refl
  merge/clocked/cost≤merge/clocked/cost/closed (suc k) ([]     , l₂    ) u = z≤n
  merge/clocked/cost≤merge/clocked/cost/closed (suc k) (x ∷ xs , []    ) u = z≤n
  merge/clocked/cost≤merge/clocked/cost/closed (suc k) (x ∷ xs , y ∷ ys) u with h-cost x y
  ... | ⇓ false withCost q [ _ , h-eq ] rewrite eq/ref h-eq =
    let (l , ≡ , _) = merge/clocked/correct k (x ∷ xs) ys u in
    begin
      step cost q (1 + bind cost (merge/clocked k (x ∷ xs , ys)) (λ l → merge/clocked/cost k (x ∷ xs , ys) + 0))
    ≡⟨ step/ext cost _ q u ⟩
      1 + bind cost (merge/clocked k (x ∷ xs , ys)) (λ l → merge/clocked/cost k (x ∷ xs , ys) + 0)
    ≡⟨⟩
      suc (bind cost (merge/clocked k (x ∷ xs , ys)) (λ l → merge/clocked/cost k (x ∷ xs , ys) + 0))
    ≡⟨ Eq.cong (λ e → suc (bind cost e λ l → merge/clocked/cost k (x ∷ xs , ys) + 0)) (≡) ⟩
      suc (merge/clocked/cost k (x ∷ xs , ys) + 0)
    ≡⟨ Eq.cong suc (N.+-identityʳ _) ⟩
      suc (merge/clocked/cost k (x ∷ xs , ys))
    ≤⟨ s≤s (merge/clocked/cost≤merge/clocked/cost/closed k (x ∷ xs , ys) u) ⟩
      suc (merge/clocked/cost/closed k (x ∷ xs , ys))
    ≡⟨⟩
      suc k
    ∎
      where open ≤-Reasoning
  ... | ⇓ true withCost q [ _ , h-eq ] rewrite eq/ref h-eq =
    let (l , ≡ , _) = merge/clocked/correct k xs (y ∷ ys) u in
    begin
      step cost q (1 + bind cost (merge/clocked k (xs , y ∷ ys)) (λ l → merge/clocked/cost k (xs , y ∷ ys) + 0))
    ≡⟨ step/ext cost _ q u ⟩
      1 + bind cost (merge/clocked k (xs , y ∷ ys)) (λ l → merge/clocked/cost k (xs , y ∷ ys) + 0)
    ≡⟨⟩
      suc (bind cost (merge/clocked k (xs , y ∷ ys)) (λ l → merge/clocked/cost k (xs , y ∷ ys) + 0))
    ≡⟨ Eq.cong (λ e → suc (bind cost e λ l → merge/clocked/cost k (xs , y ∷ ys) + 0)) (≡) ⟩
      suc (merge/clocked/cost k (xs , y ∷ ys) + 0)
    ≡⟨ Eq.cong suc (N.+-identityʳ _) ⟩
      suc (merge/clocked/cost k (xs , y ∷ ys))
    ≤⟨ s≤s (merge/clocked/cost≤merge/clocked/cost/closed k (xs , y ∷ ys) u) ⟩
      suc (merge/clocked/cost/closed k (xs , y ∷ ys))
    ≡⟨⟩
      suc k
    ∎
      where open ≤-Reasoning

  merge/clocked≤merge/clocked/cost : ∀ k p → IsBounded (list A) (merge/clocked k p) (merge/clocked/cost k p)
  merge/clocked≤merge/clocked/cost zero    (l₁     , l₂    ) = bound/ret
  merge/clocked≤merge/clocked/cost (suc k) ([]     , l₂    ) = bound/relax (λ u → z≤n) bound/ret
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , []    ) = bound/relax (λ u → z≤n) bound/ret
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , y ∷ ys) =
    bound/bind 1 _ (h-cost x y) λ b →
      bound/bool {p = λ b → if_then_else_ b _ _} b
        (bound/bind (merge/clocked/cost k (x ∷ xs , ys)) _ (merge/clocked≤merge/clocked/cost k (x ∷ xs , ys)) λ l → bound/ret)
        (bound/bind (merge/clocked/cost k (xs , y ∷ ys)) _ (merge/clocked≤merge/clocked/cost k (xs , y ∷ ys)) λ l → bound/ret)

  merge/clocked≤merge/clocked/cost/closed : ∀ k p → IsBounded (list A) (merge/clocked k p) (merge/clocked/cost/closed k p)
  merge/clocked≤merge/clocked/cost/closed k p = bound/relax (merge/clocked/cost≤merge/clocked/cost/closed k p) (merge/clocked≤merge/clocked/cost k p)

  merge : cmp (Π pair λ _ → F (list A))
  merge (l₁ , l₂) = merge/clocked (length l₁ + length l₂) (l₁ , l₂)

  merge/correct : ∀ l₁ l₂ →
    ◯ (∃ λ l → merge (l₁ , l₂) ≡ ret l × (Sorted l₁ → Sorted l₂ → SortedOf (l₁ ++ l₂) l))
  merge/correct l₁ l₂ u =
    let (l , ≡ , h-sorted) = merge/clocked/correct (length l₁ + length l₂) l₁ l₂ u in
    l , ≡ , h-sorted N.≤-refl

  merge/cost : cmp (Π pair λ _ → cost)
  merge/cost (l₁ , l₂) = merge/clocked/cost (length l₁ + length l₂) (l₁ , l₂)

  merge/cost/closed : cmp (Π pair λ _ → cost)
  merge/cost/closed (l₁ , l₂) = merge/clocked/cost/closed (length l₁ + length l₂) (l₁ , l₂)

  merge≤merge/cost : ∀ p → IsBounded (list A) (merge p) (merge/cost p)
  merge≤merge/cost (l₁ , l₂) = merge/clocked≤merge/clocked/cost (length l₁ + length l₂) (l₁ , l₂)

  merge≤merge/cost/closed : ∀ p → IsBounded (list A) (merge p) (merge/cost/closed p)
  merge≤merge/cost/closed (l₁ , l₂) = merge/clocked≤merge/clocked/cost/closed (length l₁ + length l₂) (l₁ , l₂)

  sort/clocked : cmp (Π nat λ _ → Π (list A) λ _ → F (list A))
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
                                      ≤⟨ log₂-suc (length l) h ⟩
                                        k
                                      ∎
                                    ) u in
    let (l₂' , ≡₂ , ↭₂ , sorted₂) = sort/clocked/correct k l₂ (
                                      let open ≤-Reasoning in
                                      begin
                                        ⌈log₂ length l₂ ⌉
                                      ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
                                        ⌈log₂ ⌈ length l /2⌉ ⌉
                                      ≤⟨ log₂-suc (length l) h ⟩
                                        k
                                      ∎
                                    ) u in
    let (l' , ≡' , h-sorted) = merge/correct l₁' l₂' u
        (↭' , sorted) = h-sorted sorted₁ sorted₂
    in
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
      ↭⟨ ++⁺-↭ ↭₁ ↭₂ ⟩
        l₁' ++ l₂'
      ↭⟨ ↭' ⟩
        l'
      ∎
    ) , sorted

  sort/clocked/cost : cmp (Π nat λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost zero    l = zero
  sort/clocked/cost (suc k) l =
    bind cost (split l) λ (l₁ , l₂) → split/cost l +
      bind cost (sort/clocked k l₁) λ l₁' → sort/clocked/cost k l₁ +
        bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
          merge/cost/closed (l₁' , l₂')

  sort/clocked/cost/closed : cmp (Π nat λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost/closed k l = k * length l

  sort/clocked/cost≡sort/clocked/cost/closed : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → ◯ (sort/clocked/cost k l ≡ sort/clocked/cost/closed k l)
  sort/clocked/cost≡sort/clocked/cost/closed zero    l h u = refl
  sort/clocked/cost≡sort/clocked/cost/closed (suc k) l h u =
    let (l₁ , l₂ , ≡ , length₁ , length₂ , ↭) = split/correct l u in
    let h₁ : ⌈log₂ length l₁ ⌉ Nat.≤ k
        h₁ =
          let open ≤-Reasoning in
          begin
            ⌈log₂ length l₁ ⌉
          ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
            ⌈log₂ ⌊ length l /2⌋ ⌉
          ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
            ⌈log₂ ⌈ length l /2⌉ ⌉
          ≤⟨ log₂-suc (length l) h ⟩
            k
          ∎

        h₂ : ⌈log₂ length l₂ ⌉ Nat.≤ k
        h₂ =
          let open ≤-Reasoning in
          begin
            ⌈log₂ length l₂ ⌉
          ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
            ⌈log₂ ⌈ length l /2⌉ ⌉
          ≤⟨ log₂-suc (length l) h ⟩
            k
          ∎
    in
    let (l₁' , ≡₁ , ↭₁ , sorted₁) = sort/clocked/correct k l₁ h₁ u in
    let (l₂' , ≡₂ , ↭₂ , sorted₂) = sort/clocked/correct k l₂ h₂ u in
    let open ≡-Reasoning in
    begin
      sort/clocked/cost (suc k) l
    ≡⟨⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l +
        bind cost (sort/clocked k l₁) λ l₁' → sort/clocked/cost k l₁ +
          bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
            merge/cost/closed (l₁' , l₂'))
    ≡⟨ Eq.cong (λ e → bind cost e _) (≡) ⟩
      (split/cost l +
        bind cost (sort/clocked k l₁) λ l₁' → sort/clocked/cost k l₁ +
          bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
            merge/cost/closed (l₁' , l₂'))
    ≡⟨⟩
      (0 +
        bind cost (sort/clocked k l₁) λ l₁' → sort/clocked/cost k l₁ +
          bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
            merge/cost/closed (l₁' , l₂'))
    ≡⟨ N.+-identityˡ _ ⟩
      (bind cost (sort/clocked k l₁) λ l₁' → sort/clocked/cost k l₁ +
        bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
          merge/cost/closed (l₁' , l₂'))
    ≡⟨
      Eq.cong
        (λ e →
          bind cost e λ l₁' → sort/clocked/cost k l₁ +
            bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
              merge/cost/closed (l₁' , l₂'))
        ≡₁
    ⟩
      (sort/clocked/cost k l₁ +
        bind cost (sort/clocked k l₂) λ l₂' → sort/clocked/cost k l₂ +
          merge/cost/closed (l₁' , l₂'))
    ≡⟨
      Eq.cong
        (λ e →
          sort/clocked/cost k l₁ +
            bind cost e λ l₂' → sort/clocked/cost k l₂ +
              merge/cost/closed (l₁' , l₂'))
        ≡₂
    ⟩
      sort/clocked/cost k l₁ + (sort/clocked/cost k l₂ + merge/cost/closed (l₁' , l₂'))
    ≡˘⟨ N.+-assoc (sort/clocked/cost k l₁) (sort/clocked/cost k l₂) (merge/cost/closed (l₁' , l₂')) ⟩
      (sort/clocked/cost k l₁ + sort/clocked/cost k l₂) + merge/cost/closed (l₁' , l₂')
    ≡⟨
      Eq.cong (_+ merge/cost/closed (l₁' , l₂')) (
        Eq.cong₂ _+_
          (sort/clocked/cost≡sort/clocked/cost/closed k l₁ h₁ u)
          (sort/clocked/cost≡sort/clocked/cost/closed k l₂ h₂ u)
      )
    ⟩
      (sort/clocked/cost/closed k l₁ + sort/clocked/cost/closed k l₂) + merge/cost/closed (l₁' , l₂')
    ≡⟨⟩
      (sort/clocked/cost/closed k l₁ + sort/clocked/cost/closed k l₂) + (length l₁' + length l₂')
    ≡˘⟨
      Eq.cong ((sort/clocked/cost/closed k l₁ + sort/clocked/cost/closed k l₂) +_) (
        Eq.cong₂ _+_ (↭-length ↭₁) (↭-length ↭₂)
      )
    ⟩
      (sort/clocked/cost/closed k l₁ + sort/clocked/cost/closed k l₂) + (length l₁ + length l₂)
    ≡⟨⟩
      (k * length l₁ + k * length l₂) + (length l₁ + length l₂)
    ≡⟨
      Eq.cong₂
        (λ n₁ n₂ → k * n₁ + k * n₂ + (n₁ + n₂))
        length₁
        length₂
    ⟩
      (k * ⌊ length l /2⌋ + k * ⌈ length l /2⌉) + (⌊ length l /2⌋ + ⌈ length l /2⌉)
    ≡⟨ N.+-comm _ (⌊ length l /2⌋ + ⌈ length l /2⌉) ⟩
      (⌊ length l /2⌋ + ⌈ length l /2⌉) + (k * ⌊ length l /2⌋ + k * ⌈ length l /2⌉)
    ≡˘⟨ Eq.cong ((⌊ length l /2⌋ + ⌈ length l /2⌉) +_) (N.*-distribˡ-+ k _ _) ⟩
      (⌊ length l /2⌋ + ⌈ length l /2⌉) + k * (⌊ length l /2⌋ + ⌈ length l /2⌉)
    ≡⟨⟩
      suc k * (⌊ length l /2⌋ + ⌈ length l /2⌉)
    ≡⟨ Eq.cong (suc k *_) (N.⌊n/2⌋+⌈n/2⌉≡n (length l)) ⟩
      suc k * length l
    ∎

  sort/clocked≤sort/clocked/cost : ∀ k l → IsBounded (list A) (sort/clocked k l) (sort/clocked/cost k l)
  sort/clocked≤sort/clocked/cost zero l = bound/ret
  sort/clocked≤sort/clocked/cost (suc k) l =
    bound/bind _ _ (split≤split/cost l) λ (l₁ , l₂) →
      bound/bind _ _ (sort/clocked≤sort/clocked/cost k l₁) λ l₁' →
        bound/bind _ _ (sort/clocked≤sort/clocked/cost k l₂) λ l₂' →
          merge≤merge/cost/closed (l₁' , l₂')

  sort/clocked≤sort/clocked/cost/closed : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → IsBounded (list A) (sort/clocked k l) (sort/clocked/cost/closed k l)
  sort/clocked≤sort/clocked/cost/closed k l h = bound/relax (λ u → N.≤-reflexive (sort/clocked/cost≡sort/clocked/cost/closed k l h u)) (sort/clocked≤sort/clocked/cost k l)

  sort/depth : cmp (Π (list A) λ _ → meta ℕ)
  sort/depth l = ⌈log₂ length l ⌉

  sort : cmp (Π (list A) λ _ → F (list A))
  sort l = sort/clocked (sort/depth l) l

  sort/correct : IsSort sort
  sort/correct l = sort/clocked/correct (sort/depth l) l N.≤-refl

  sort/cost : cmp (Π (list A) λ _ → cost)
  sort/cost l = sort/clocked/cost (sort/depth l) l

  sort/cost/closed : cmp (Π (list A) λ _ → cost)
  sort/cost/closed l = sort/clocked/cost/closed (sort/depth l) l

  sort≤sort/cost : ∀ l → IsBounded (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

  sort≤sort/cost/closed : ∀ l → IsBounded (list A) (sort l) (sort/cost/closed l)
  sort≤sort/cost/closed l = sort/clocked≤sort/clocked/cost/closed (sort/depth l) l N.≤-refl

module Ex/MergeSort where
  module Sort = MergeSort NatComparable

  list' = list nat

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
