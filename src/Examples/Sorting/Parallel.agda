{-# OPTIONS --prop --rewriting #-}

module Examples.Sorting.Parallel where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid
  renaming (
    _≤_ to _P≤_;
    ≤-refl to P≤-refl;
    ≤-trans to P≤-trans;
    module ≤-Reasoning to P≤-Reasoning
  )

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool
open import Calf.Types.List as List

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_; ⌊_/2⌋; ⌈_/2⌉; pred; _⊔_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)

private
  variable
    α : Set

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
    h-cost : (x y : val A) → ub bool (x ≤ᵇ y) (1 , 1)

NatComparable : Comparable
NatComparable = record
  { A = U (meta ℕ)
  ; _≤_ = _≤_
  ; _≤ᵇ_ = λ x y → step' (F bool) (1 , 1) (ret (x ≤ᵇ y))
  ; ≤ᵇ-reflects-≤ = reflects
  ; ≤-refl = ≤-refl
  ; ≤-trans = ≤-trans
  ; ≤-total = ≤-total
  ; ≤-antisym = ≤-antisym
  ; h-cost = λ _ _ → ub/step (1 , 1) 𝟘 ub/ret
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

    ret-injective : ∀ {𝕊 v₁ v₂} → ret {U (meta 𝕊)} v₁ ≡ ret {U (meta 𝕊)} v₂ → v₁ ≡ v₂
    ret-injective {𝕊} = Eq.cong (λ e → bind {U (meta 𝕊)} (meta 𝕊) e id)

    reflects : ∀ {m n b} → ◯ (step' (F bool) (1 , 1) (ret (m ≤ᵇ n)) ≡ ret {bool} b → Reflects (m ≤ n) b)
    reflects {m} {n} {b} u h with ret-injective (Eq.subst (_≡ ret b) (step'/ext (F bool) (ret (m ≤ᵇ n)) (1 , 1) u) h)
    ... | refl = ≤ᵇ-reflects-≤ m n

module Core (M : Comparable) where
  open Comparable M

  open import Data.List.Relation.Binary.Permutation.Propositional public
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (¬x∷xs↭[]; All-resp-↭; Any-resp-↭; drop-∷)
    renaming (++-comm to ++-comm-↭; ++⁺ˡ to ++⁺ˡ-↭; ++⁺ʳ to ++⁺ʳ-↭; ++⁺ to ++⁺-↭) public
  open import Data.List.Relation.Unary.All using (All; []; _∷_; map; lookup) public
  open import Data.List.Relation.Unary.All.Properties as AllP using () renaming (++⁺ to ++⁺-All) public
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

  join-sorted : ∀ {l₁ mid l₂} → Sorted l₁ → Sorted l₂ → All (_≤ mid) l₁ → All (mid ≤_) l₂ → Sorted (l₁ ++ [ mid ] ++ l₂)
  join-sorted []            sorted₂ all₁        all₂ = all₂ ∷ sorted₂
  join-sorted (h ∷ sorted₁) sorted₂ (h' ∷ all₁) all₂ =
    ++⁺-All h (h' ∷ ≤-≤* h' all₂) ∷ (join-sorted sorted₁ sorted₂ all₁ all₂)

  ++⁻ˡ : ∀ xs {ys} → Sorted (xs ++ ys) → Sorted xs
  ++⁻ˡ []       sorted       = []
  ++⁻ˡ (x ∷ xs) (h ∷ sorted) = AllP.++⁻ˡ xs h ∷ (++⁻ˡ xs sorted)

  ++⁻ʳ : ∀ xs {ys} → Sorted (xs ++ ys) → Sorted ys
  ++⁻ʳ []       sorted       = sorted
  ++⁻ʳ (x ∷ xs) (h ∷ sorted) = ++⁻ʳ xs sorted

  uncons₁ : ∀ {x xs} → Sorted (x ∷ xs) → x ≤* xs
  uncons₁ (h ∷ sorted) = h

  uncons₂ : ∀ {x xs} → Sorted (x ∷ xs) → Sorted xs
  uncons₂ (h ∷ sorted) = sorted

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
    ) , All-resp-↭ x∷ys↭ys' (x≤y ∷ h) ∷ sorted-ys'
  insert/correct x (y ∷ ys) (h ∷ hs) u | ub/intro {q = q} true _ _ | ofʸ x≤y | _ =
    x ∷ (y ∷ ys) , step'/ext (F (list A)) (ret _) q u , refl , (x≤y ∷ ≤-≤* x≤y h) ∷ (h ∷ hs)

  insert/length : ∀ x l (κ : ℕ → α) → bind (meta α) (insert x l) (κ ∘ length) ≡ κ (suc (length l))
  insert/length x []       κ = refl
  insert/length x (y ∷ ys) κ with h-cost x y
  ... | ub/intro false _ h-eq rewrite eq/ref h-eq = insert/length x ys (κ ∘ suc)
  ... | ub/intro true  _ h-eq rewrite eq/ref h-eq = refl

  insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost x []       = 𝟘
  insert/cost x (y ∷ ys) with h-cost x y
  ... | ub/intro {q = q} false q≤1 h-eq = q ⊕ (insert/cost x ys ⊕ 𝟘)
  ... | ub/intro {q = q} true  q≤1 h-eq = q ⊕ 𝟘

  insert/cost/closed : cmp (Π A λ _ → Π (list A) λ _ → cost)
  insert/cost/closed x l = length l , length l
 
  insert/cost≤insert/cost/closed : ∀ x l → insert/cost x l P≤ insert/cost/closed x l
  insert/cost≤insert/cost/closed x []       = P≤-refl
  insert/cost≤insert/cost/closed x (y ∷ ys) with h-cost x y
  ... | ub/intro {q = q} false q≤1 h-eq =
    Eq.subst (λ n → (q ⊕ n) P≤ (suc (length ys) , suc (length ys))) (Eq.sym (⊕-identityʳ (insert/cost x ys))) (
      P≤-trans
        (⊕-monoˡ-≤ _ q≤1)
        (s≤s (proj₁ (insert/cost≤insert/cost/closed x ys)) ,
         s≤s (proj₂ (insert/cost≤insert/cost/closed x ys)))
    )
  ... | ub/intro {q = q} true  q≤1 h-eq =
    Eq.subst (_P≤ (suc (length ys) , suc (length ys))) (Eq.sym (⊕-identityʳ q)) (
      P≤-trans q≤1 (s≤s z≤n , s≤s z≤n)
    )

  insert≤insert/cost : ∀ x l → ub (list A) (insert x l) (insert/cost x l)
  insert≤insert/cost x []       = ub/ret
  insert≤insert/cost x (y ∷ ys) with h-cost x y
  ... | ub/intro {q = q} false q≤1 h-eq rewrite eq/ref h-eq =
    ub/step q (insert/cost x ys ⊕ 𝟘) (ub/bind/const (insert/cost x ys) 𝟘 (insert≤insert/cost x ys) λ _ → ub/ret)
  ... | ub/intro {q = q} true  q≤1 h-eq rewrite eq/ref h-eq =
    ub/step q 𝟘 ub/ret

  insert≤insert/cost/closed : ∀ x l → ub (list A) (insert x l) (insert/cost/closed x l)
  insert≤insert/cost/closed x l = ub/relax (insert/cost≤insert/cost/closed x l) (insert≤insert/cost x l)

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
  sort/cost []       = 𝟘
  sort/cost (x ∷ xs) = bind cost (sort xs) (λ xs' → sort/cost xs ⊕ insert/cost/closed x xs')

  sort/cost/closed : cmp (Π (list A) λ _ → cost)
  sort/cost/closed l = length l ^ 2 , length l ^ 2

  sort/cost≤sort/cost/closed : ∀ l → sort/cost l P≤ sort/cost/closed l
  sort/cost≤sort/cost/closed []       = P≤-refl
  sort/cost≤sort/cost/closed (x ∷ xs) =
    let open P≤-Reasoning in
    begin
      sort/cost (x ∷ xs)
    ≡⟨⟩
      bind cost (sort xs) (λ xs' → sort/cost xs ⊕ insert/cost/closed x xs')
    ≡⟨ sort/length xs (λ n → sort/cost xs ⊕ (n , n)) ⟩
      sort/cost xs ⊕ insert/cost/closed x xs
    ≤⟨ ⊕-monoˡ-≤ (insert/cost/closed x xs) (sort/cost≤sort/cost/closed xs) ⟩
      sort/cost/closed xs ⊕ insert/cost/closed x xs
    ≡⟨⟩
      (length xs ^ 2 , length xs ^ 2) ⊕ (length xs , length xs)
    ≤⟨ lemma/arithmetic (length xs) , lemma/arithmetic (length xs) ⟩
      length (x ∷ xs) ^ 2 , length (x ∷ xs) ^ 2
    ≡⟨⟩
      sort/cost/closed (x ∷ xs)
    ∎
      where
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
          where open ≤-Reasoning

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost []       = ub/ret
  sort≤sort/cost (x ∷ xs) = ub/bind (sort/cost xs) (insert/cost/closed x) (sort≤sort/cost xs) (insert≤insert/cost/closed x)

  sort≤sort/cost/closed : ∀ l → ub (list A) (sort l) (sort/cost/closed l)
  sort≤sort/cost/closed l = ub/relax (sort/cost≤sort/cost/closed l) (sort≤sort/cost l)

module Ex/InsertionSort where
  module Sort = InsertionSort NatComparable

  list' = list (U (meta ℕ))

  ex/insert : cmp (F list')
  ex/insert = Sort.insert 3 (1 ∷ 2 ∷ 4 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: 15 , 15

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: 120 , 120

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: 76 , 76

module Log2 where
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

module MergeSort (M : Comparable) where
  open Comparable M
  open Core M
  open Log2

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ {x} {y} h with ≤-total x y
  ... | inj₁ h₁ = ⊥-elim (h h₁)
  ... | inj₂ h₂ = h₂

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
  split/clocked/cost _ _ = 𝟘

  split/clocked≤split/clocked/cost : ∀ k l → ub pair (split/clocked k l) (split/clocked/cost k l)
  split/clocked≤split/clocked/cost zero    l        = ub/ret
  split/clocked≤split/clocked/cost (suc k) []       = ub/ret
  split/clocked≤split/clocked/cost (suc k) (x ∷ xs) = ub/bind/const 𝟘 𝟘 (split/clocked≤split/clocked/cost k xs) λ _ → ub/ret

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
      ↭⟨ ++-comm-↭ (x ∷ xs) (y ∷ ys) ⟩
        (y ∷ ys ++ x ∷ xs)
      ≡⟨⟩
        y ∷ (ys ++ x ∷ xs)
      <⟨ ++-comm-↭ ys (x ∷ xs) ⟩
        y ∷ (x ∷ xs ++ ys)
      <⟨ ↭ ⟩
        y ∷ l
      ∎
     ) , All-resp-↭ (↭) (++⁺-All (p ∷ ≤-≤* p h₁) h₂) ∷ sorted
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
    ) , prep x ↭ , All-resp-↭ (↭) (++⁺-All h₁ (p ∷ ≤-≤* p h₂)) ∷ sorted

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
  merge/clocked/cost k _ = k , k

  merge/clocked≤merge/clocked/cost : ∀ k p → ub (list A) (merge/clocked k p) (merge/clocked/cost k p)
  merge/clocked≤merge/clocked/cost zero    (l₁     , l₂    ) = ub/ret
  merge/clocked≤merge/clocked/cost (suc k) ([]     , l₂    ) = ub/relax (z≤n , z≤n) ub/ret
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , []    ) = ub/relax (z≤n , z≤n) ub/ret
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , y ∷ ys) =
    ub/bind/const (1 , 1) (k , k) (h-cost x y)
      λ { false → ub/bind/const' (k , k) 𝟘 (⊕-identityʳ _) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret
        ; true  → ub/bind/const' (k , k) 𝟘 (⊕-identityʳ _) (merge/clocked≤merge/clocked/cost k _) λ _ → ub/ret }

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
      bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge

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
    let (l' , ≡' , ↭' , sorted) = merge/correct l₁' l₂' sorted₁ sorted₂ u in
    l' , (
      let open ≡-Reasoning in
      begin
        sort/clocked (suc k) l
      ≡⟨⟩
        (bind (F (list A)) (split l) λ (l₁ , l₂) →
          bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge)
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e merge) (Eq.cong₂ _&_ ≡₁ ≡₂) ⟩
        bind (F (list A)) (ret l₁' & ret l₂') merge
      ≡⟨ bind/par 𝟘 𝟘 ⟩
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

  sort/clocked/length : ∀ k l (κ : ℕ → α) → bind (meta α) (sort/clocked k l) (κ ∘ length) ≡ κ (length l)
  sort/clocked/length {_} zero    l κ = refl
  sort/clocked/length {α} (suc k) l κ =
    begin
      bnd (sort/clocked (suc k) l) (κ ∘ length)
    ≡⟨⟩
      (bnd (split l) λ (l₁ , l₂) →
        bnd (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') →
          bnd (merge (l₁' , l₂')) (κ ∘ length))
    ≡⟨
      Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) →
        Eq.cong (bnd (sort/clocked k l₁ & sort/clocked k l₂)) (funext λ (l₁' , l₂') →
          merge/length l₁' l₂' κ
        )
      )
    ⟩
      (bnd (split l) λ (l₁ , l₂) →
        bnd (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') →
          κ (length l₁' + length l₂'))
    ≡⟨
      Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) →
        bind/par/seq
          {κ = λ (l₁' , l₂') → κ (length l₁' + length l₂')}
          {e₁ = sort/clocked k l₁}
          {e₂ = sort/clocked k l₂}
      )
    ⟩
      (bnd (split l) λ (l₁ , l₂) →
        bnd (sort/clocked k l₁) λ l₁' →
          bnd (sort/clocked k l₂) λ l₂' →
            κ (length l₁' + length l₂'))
    ≡⟨
      Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) →
        Eq.cong (bnd (sort/clocked k l₁)) (funext λ l₁' →
          sort/clocked/length k l₂ λ n₂ →
            κ (length l₁' + n₂)
        )
      )
    ⟩
      (bnd (split l) λ (l₁ , l₂) →
        bnd (sort/clocked k l₁) λ l₁' →
          κ (length l₁' + length l₂))
    ≡⟨
      Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) →
        sort/clocked/length k l₁ λ n₁ →
          κ (n₁ + length l₂)
      )
    ⟩
      (bnd (split l) λ (l₁ , l₂) →
        κ (length l₁ + length l₂))
    ≡⟨ split/length l (λ n₁ n₂ → κ (n₁ + n₂)) ⟩
      κ (⌊ length l /2⌋ + ⌈ length l /2⌉ )
    ≡⟨ Eq.cong κ (N.⌊n/2⌋+⌈n/2⌉≡n (length l)) ⟩
      κ (length l)
    ∎
    where
      open ≡-Reasoning

      bnd : ∀ {A} → cmp (F A) → (val A → α) → α
      bnd = bind (meta α)

  sort/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost zero    l = 𝟘
  sort/clocked/cost (suc k) l =
    bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
      bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost (l₁' , l₂')

  sort/clocked/cost/closed : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost/closed k l = k * length l , 2 * length l + k

  sort/clocked/cost≤sort/clocked/cost/closed : ∀ k l → sort/clocked/cost k l P≤ sort/clocked/cost/closed k l
  sort/clocked/cost≤sort/clocked/cost/closed zero    l = z≤n , z≤n
  sort/clocked/cost≤sort/clocked/cost/closed (suc k) l =
    let open P≤-Reasoning in
    begin
      sort/clocked/cost (suc k) l
    ≡⟨⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
          merge/cost (l₁' , l₂'))
    ≡⟨⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
          (length l₁' + length l₂' , length l₁' + length l₂'))
    ≡⟨
      Eq.cong (bind cost (split l)) (funext λ (l₁ , l₂) → Eq.cong (split/cost l ⊕_) (
        bind/par/seq
          {κ = λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕ (length l₁' + length l₂' , length l₁' + length l₂')}
          {e₁ = sort/clocked k l₁}
          {e₂ = sort/clocked k l₂}
      ))
    ⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        bind cost (sort/clocked k l₁) λ l₁' →
          bind cost (sort/clocked k l₂) λ l₂' → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
            (length l₁' + length l₂' , length l₁' + length l₂'))
    ≡⟨
      Eq.cong (bind cost (split l)) (funext λ (l₁ , l₂) → Eq.cong (split/cost l ⊕_) (
        sort/clocked/length k l₁ λ n₁ →
          bind cost (sort/clocked k l₂) λ l₂' → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
            (n₁ + length l₂' , n₁ + length l₂')
      ))
    ⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        bind cost (sort/clocked k l₂) λ l₂' → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
          (length l₁ + length l₂' , length l₁ + length l₂'))
    ≡⟨
      Eq.cong (bind cost (split l)) (funext λ (l₁ , l₂) → Eq.cong (split/cost l ⊕_) (
        sort/clocked/length k l₂ λ n₂ → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
            (length l₁ + n₂ , length l₁ + n₂)
      ))
    ⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        ((sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
          (length l₁ + length l₂ , length l₁ + length l₂)))
    ≤⟨
      Eq.subst
        id
        (Eq.sym (
          tbind/meta'
            pair
            ℂ
            ℂ
            (split l)
            (λ (l₁ , l₂) → split/cost l ⊕ ((sort/clocked/cost        k l₁ ⊗ sort/clocked/cost        k l₂) ⊕ (length l₁ + length l₂ , length l₁ + length l₂)))
            (λ (l₁ , l₂) → split/cost l ⊕ ((sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕ (length l₁ + length l₂ , length l₁ + length l₂)))
            _P≤_
        ))
        (dbind
          (λ (l₁ , l₂) → meta (
            (split/cost l ⊕ ((sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕ (length l₁ + length l₂ , length l₁ + length l₂)))
            P≤
            (split/cost l ⊕ ((sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕ (length l₁ + length l₂ , length l₁ + length l₂)))
          ))
          (split l)
          λ (l₁ , l₂) →
            ⊕-monoʳ-≤ 𝟘 (
              ⊕-monoˡ-≤ (length l₁ + length l₂ , length l₁ + length l₂) (
                ⊗-mono-≤
                  (sort/clocked/cost≤sort/clocked/cost/closed k l₁)
                  (sort/clocked/cost≤sort/clocked/cost/closed k l₂)
              )
            )
        )
    ⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        ((sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕
          (length l₁ + length l₂ , length l₁ + length l₂)))
    ≡⟨⟩
      (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
        (((k * length l₁ , 2 * length l₁ + k) ⊗ (k * length l₂ , 2 * length l₂ + k)) ⊕
          (length l₁ + length l₂ , length l₁ + length l₂)))
    ≡⟨ split/length l (λ n₁ n₂ → ((k * n₁ , 2 * n₁ + k) ⊗ (k * n₂ , 2 * n₂ + k)) ⊕ (n₁ + n₂ , n₁ + n₂)) ⟩
      (split/cost l ⊕
        ((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕
          (⌊ length l /2⌋ + ⌈ length l /2⌉ , ⌊ length l /2⌋ + ⌈ length l /2⌉))
    ≡⟨ ⊕-identityˡ _ ⟩
      ((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕
        (⌊ length l /2⌋ + ⌈ length l /2⌉ , ⌊ length l /2⌋ + ⌈ length l /2⌉)
    ≡⟨
      Eq.cong (((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕_) (
        Eq.cong₂ _,_ (N.⌊n/2⌋+⌈n/2⌉≡n (length l)) (N.⌊n/2⌋+⌈n/2⌉≡n (length l))
      )
    ⟩
      ((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕
        (length l , length l)
    ≤⟨ arithmetic/work (length l) , arithmetic/span (length l) ⟩
      suc k * length l , 2 * length l + suc k
    ≡⟨⟩
      sort/clocked/cost/closed (suc k) l
    ∎
      where
        arithmetic/work : ∀ n → k * ⌊ n /2⌋ + k * ⌈ n /2⌉ + n Nat.≤ suc k * n
        arithmetic/work n =
          begin
            k * ⌊ n /2⌋ + k * ⌈ n /2⌉ + n
          ≡⟨ N.+-comm _ n ⟩
            n + (k * ⌊ n /2⌋ + k * ⌈ n /2⌉)
          ≡˘⟨ Eq.cong₂ (_+_) (N.*-identityˡ _) (N.*-distribˡ-+ k _ _) ⟩
            1 * n + k * (⌊ n /2⌋ + ⌈ n /2⌉)
          ≡⟨ Eq.cong (λ m → 1 * n + k * m) (N.⌊n/2⌋+⌈n/2⌉≡n n) ⟩
            1 * n + k * n
          ≡˘⟨ N.*-distribʳ-+ _ 1 k ⟩
            suc k * n
          ∎
            where open ≤-Reasoning

        lemma/2n≡n+n : ∀ n → 2 * n ≡ n + n
        lemma/2n≡n+n n = Eq.cong (λ m → n + m) (N.+-identityʳ n)

        arithmetic/span : ∀ n → (2 * ⌊ n /2⌋ + k) ⊔ (2 * ⌈ n /2⌉ + k) + n Nat.≤ 2 * n + suc k
        arithmetic/span n =
          begin
            (2 * ⌊ n /2⌋ + k) ⊔ (2 * ⌈ n /2⌉ + k) + n
          ≤⟨ N.+-monoˡ-≤ n (N.⊔-monoˡ-≤ (2 * ⌈ n /2⌉ + k) (N.+-monoˡ-≤ k (N.*-monoʳ-≤ 2 (N.⌊n/2⌋≤⌈n/2⌉ n)))) ⟩
            (2 * ⌈ n /2⌉ + k) ⊔ (2 * ⌈ n /2⌉ + k) + n
          ≡⟨ Eq.cong (_+ n) (N.⊔-idem _) ⟩
            2 * ⌈ n /2⌉ + k + n
          ≡⟨ N.+-assoc (2 * ⌈ n /2⌉) k n ⟩
            2 * ⌈ n /2⌉ + (k + n)
          ≡⟨ Eq.cong (_+ (k + n)) (lemma/2n≡n+n ⌈ n /2⌉) ⟩
            (⌈ n /2⌉ + ⌈ n /2⌉) + (k + n)
          ≡⟨⟩
            (⌊ suc n /2⌋ + ⌈ n /2⌉) + (k + n)
          ≤⟨ N.+-monoˡ-≤ (k + n) (N.+-monoʳ-≤ ⌊ suc n /2⌋ (N.⌈n/2⌉-mono (N.n≤1+n n))) ⟩
            (⌊ suc n /2⌋ + ⌈ suc n /2⌉) + (k + n)
          ≡⟨ Eq.cong (_+ (k + n)) (N.⌊n/2⌋+⌈n/2⌉≡n (suc n)) ⟩
            suc n + (k + n)
          ≡⟨⟩
            suc (n + (k + n))
          ≡⟨ Eq.cong (λ m → suc (n + m)) (N.+-comm k n) ⟩
            suc (n + (n + k))
          ≡˘⟨ Eq.cong suc (N.+-assoc n n k) ⟩
            suc ((n + n) + k)
          ≡˘⟨ N.+-suc (n + n) k ⟩
            (n + n) + suc k
          ≡˘⟨ Eq.cong (_+ suc k) (lemma/2n≡n+n n) ⟩
            2 * n + suc k
          ∎
            where open ≤-Reasoning

  sort/clocked≤sort/clocked/cost : ∀ k l → ub (list A) (sort/clocked k l) (sort/clocked/cost k l)
  sort/clocked≤sort/clocked/cost zero l = ub/ret
  sort/clocked≤sort/clocked/cost (suc k) l =
    ub/bind _ _ (split≤split/cost l) λ (l₁ , l₂) →
      ub/bind _ _ (ub/par (sort/clocked≤sort/clocked/cost k l₁) (sort/clocked≤sort/clocked/cost k l₂)) λ (l₁' , l₂') →
        merge≤merge/cost (l₁' , l₂')

  sort/clocked≤sort/clocked/cost/closed : ∀ k l → ub (list A) (sort/clocked k l) (sort/clocked/cost/closed k l)
  sort/clocked≤sort/clocked/cost/closed k l = ub/relax (sort/clocked/cost≤sort/clocked/cost/closed k l) (sort/clocked≤sort/clocked/cost k l)

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

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

  sort≤sort/cost/closed : ∀ l → ub (list A) (sort l) (sort/cost/closed l)
  sort≤sort/cost/closed l = sort/clocked≤sort/clocked/cost/closed (sort/depth l) l

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
  ex/sort/forward = Sort.sort test/forward  -- cost: ?

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: ?

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: ?

module PredExp2 where
  pred[2^_] : ℕ → ℕ
  pred[2^ n ] = pred (2 ^ n)

  pred[2^suc[n]] : (n : ℕ) → suc (pred[2^ n ] + pred[2^ n ]) ≡ pred[2^ suc n ]
  pred[2^suc[n]] n =
    begin
      suc (pred[2^ n ] + pred[2^ n ])
    ≡⟨⟩
      suc (pred (2 ^ n) + pred (2 ^ n))
    ≡˘⟨ N.+-suc (pred (2 ^ n)) (pred (2 ^ n)) ⟩
      pred (2 ^ n) + suc (pred (2 ^ n))
    ≡⟨ Eq.cong (pred (2 ^ n) +_) (N.suc[pred[n]]≡n (lemma/2^n≢0 n)) ⟩
      pred (2 ^ n) + 2 ^ n
    ≡⟨ lemma/pred-+ (2 ^ n) (2 ^ n) (lemma/2^n≢0 n) ⟩
      pred (2 ^ n + 2 ^ n)
    ≡⟨ Eq.cong pred (lemma/2^suc n) ⟩
      pred (2 ^ suc n)
    ≡⟨⟩
      pred[2^ suc n ]
    ∎
      where
        open ≡-Reasoning

        lemma/2^suc : ∀ n → 2 ^ n + 2 ^ n ≡ 2 ^ suc n
        lemma/2^suc n =
          begin
            2 ^ n + 2 ^ n
          ≡˘⟨ Eq.cong ((2 ^ n) +_) (N.*-identityˡ (2 ^ n)) ⟩
            2 ^ n + (2 ^ n + 0)
          ≡⟨⟩
            2 ^ n + (2 ^ n + 0 * (2 ^ n))
          ≡⟨⟩
            2 * (2 ^ n)
          ≡⟨⟩
            2 ^ suc n
          ∎
            where open ≡-Reasoning

        lemma/2^n≢0 : ∀ n → 2 ^ n ≢ zero
        lemma/2^n≢0 n 2^n≡0 with N.m^n≡0⇒m≡0 2 n 2^n≡0
        ... | ()

        lemma/pred-+ : ∀ m n → m ≢ zero → pred m + n ≡ pred (m + n)
        lemma/pred-+ zero    n m≢zero = ⊥-elim (m≢zero refl)
        lemma/pred-+ (suc m) n m≢zero = refl

module MergeSortFast (M : Comparable) where
  open Comparable M
  open Core M
  open Log2
  open PredExp2

  _≥_ : val A → val A → Set
  x ≥ y = y ≤ x

  _≰_ : val A → val A → Set
  x ≰ y = ¬ x ≤ y

  ≰⇒≥ : _≰_ ⇒ _≥_
  ≰⇒≥ {x} {y} h with ≤-total x y
  ... | inj₁ h₁ = ⊥-elim (h h₁)
  ... | inj₂ h₂ = h₂

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
  split/clocked/cost _ _ = 𝟘

  split/clocked≤split/clocked/cost : ∀ k l → ub pair (split/clocked k l) (split/clocked/cost k l)
  split/clocked≤split/clocked/cost zero    l        = ub/ret
  split/clocked≤split/clocked/cost (suc k) []       = ub/ret
  split/clocked≤split/clocked/cost (suc k) (x ∷ xs) = ub/bind/const 𝟘 𝟘 (split/clocked≤split/clocked/cost k xs) λ _ → ub/ret

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

  triple = Σ++ (list A) λ _ → Σ++ A λ _ → (list A)

  splitMid/clocked : cmp (Π (U (meta ℕ)) λ k → Π (list A) λ l → Π (U (meta (k Nat.< length l))) λ _ → F triple)
  splitMid/clocked zero    (x ∷ xs) (s≤s h) = ret ([] , x , xs)
  splitMid/clocked (suc k) (x ∷ xs) (s≤s h) =
    bind (F triple) (splitMid/clocked k xs h) λ (l₁ , mid , l₂) → ret ((x ∷ l₁) , mid , l₂)

  splitMid/clocked/correct : ∀ k k' l h → k + suc k' ≡ length l →
    ◯ (∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → splitMid/clocked k l h ≡ ret (l₁ , mid , l₂) × length l₁ ≡ k × length l₂ ≡ k' × l ≡ (l₁ ++ [ mid ] ++ l₂))
  splitMid/clocked/correct zero    k' (x ∷ xs) (s≤s h) refl     u = [] , x , xs , refl , refl , refl , refl
  splitMid/clocked/correct (suc k) k' (x ∷ xs) (s≤s h) h-length u =
    let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct k k' xs h (N.suc-injective h-length) u in
    x ∷ l₁ , mid , l₂ , Eq.cong (λ e → bind (F triple) e _) ≡ , Eq.cong suc h₁ , h₂ , Eq.cong (x ∷_) ≡-↭

  splitMid/clocked/length : ∀ k k' l h → k + suc k' ≡ length l → (κ : ℕ → ℕ → α) →
    bind (meta α) (splitMid/clocked k l h) (λ (l₁ , _ , l₂) → κ (length l₁) (length l₂)) ≡ κ k k'
  splitMid/clocked/length zero    _  (x ∷ xs) (s≤s h) refl     κ = refl
  splitMid/clocked/length (suc k) k' (x ∷ xs) (s≤s h) h-length κ =
    splitMid/clocked/length k k' xs h (N.suc-injective h-length) λ n₁ n₂ → κ (suc n₁) n₂

  splitMid/clocked/cost : cmp (Π (U (meta ℕ)) λ k → Π (list A) λ l → Π (U (meta (k Nat.< length l))) λ _ → cost)
  splitMid/clocked/cost _ _ _ = 𝟘

  splitMid/clocked≤splitMid/clocked/cost : ∀ k l h → ub triple (splitMid/clocked k l h) (splitMid/clocked/cost k l h)
  splitMid/clocked≤splitMid/clocked/cost zero    (x ∷ xs) (s≤s h) = ub/ret
  splitMid/clocked≤splitMid/clocked/cost (suc k) (x ∷ xs) (s≤s h) =
    ub/bind/const 𝟘 𝟘 (splitMid/clocked≤splitMid/clocked/cost k xs h) λ _ → ub/ret

  splitMid : cmp (Π (list A) λ l → Π (U (meta (0 Nat.< length l))) λ _ → F triple)
  splitMid (x ∷ xs) (s≤s h) = splitMid/clocked ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (s≤s (N.⌈n/2⌉≤n _))

  splitMid/correct : ∀ l h →
    ◯ (∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → splitMid l h ≡ ret (l₁ , mid , l₂) × length l₁ Nat.≤ ⌊ length l /2⌋ × length l₂ Nat.≤ ⌊ length l /2⌋ × l ≡ (l₁ ++ [ mid ] ++ l₂))
  splitMid/correct (x ∷ xs) (s≤s h) u =
    let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct ⌊ length (x ∷ xs) /2⌋ ⌊ pred (length (x ∷ xs)) /2⌋ (x ∷ xs) (s≤s (N.⌈n/2⌉≤n _))
                                                (let open ≡-Reasoning in
                                                begin
                                                  ⌊ length (x ∷ xs) /2⌋ + suc ⌊ pred (length (x ∷ xs)) /2⌋
                                                ≡⟨⟩
                                                  ⌊ length (x ∷ xs) /2⌋ + suc ⌊ length xs /2⌋
                                                ≡⟨⟩
                                                  ⌈ length xs /2⌉ + suc ⌊ length xs /2⌋
                                                ≡⟨ N.+-suc ⌈ length xs /2⌉ ⌊ length xs /2⌋ ⟩
                                                  suc (⌈ length xs /2⌉ + ⌊ length xs /2⌋)
                                                ≡⟨ Eq.cong suc (N.+-comm ⌈ length xs /2⌉ ⌊ length xs /2⌋) ⟩
                                                  suc (⌊ length xs /2⌋ + ⌈ length xs /2⌉)
                                                ≡⟨ Eq.cong suc (N.⌊n/2⌋+⌈n/2⌉≡n (length xs)) ⟩
                                                  suc (length xs)
                                                ≡⟨⟩
                                                  length (x ∷ xs)
                                                ∎) u in
    l₁ , mid , l₂ , ≡ , N.≤-reflexive h₁ , (
      let open ≤-Reasoning in
      begin
        length l₂
      ≡⟨ h₂ ⟩
        ⌊ pred (length (x ∷ xs)) /2⌋
      ≤⟨ N.⌊n/2⌋-mono N.pred[n]≤n ⟩
        ⌊ length (x ∷ xs) /2⌋
      ∎
    ), ≡-↭

  splitMid/length : ∀ l h (κ : ℕ → ℕ → α) → ∃ λ n₁ → ∃ λ n₂ → n₁ Nat.≤ ⌊ length l /2⌋ × n₂ Nat.≤ ⌊ length l /2⌋ ×
    bind (meta α) (splitMid l h) (λ (l₁ , _ , l₂) → κ (length l₁) (length l₂)) ≡ κ n₁ n₂
  splitMid/length (x ∷ xs) (s≤s h) κ =
    ⌊ length (x ∷ xs) /2⌋ ,
    ⌊ pred (length (x ∷ xs)) /2⌋ ,
    N.≤-refl ,
    N.⌊n/2⌋-mono N.pred[n]≤n , (
      let open ≡-Reasoning in
      begin
        {!   !} -- splitMid/clocked/length ⌊ length l /2⌋ ⌈ length l /2⌉ l (N.⌊n/2⌋+⌈n/2⌉≡n (length l))
      ≡⟨ {!   !} ⟩
        {!   !}
      ∎
    )

  splitMid/cost : cmp (Π (list A) λ l → Π (U (meta (0 Nat.< length l))) λ _ → cost)
  splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (s≤s (N.⌈n/2⌉≤n _))

  splitMid≤splitMid/cost : ∀ l h → ub triple (splitMid l h) (splitMid/cost l h)
  splitMid≤splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked≤splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (s≤s (N.⌈n/2⌉≤n _))

  splitBy/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → Π A λ _ → F pair)
  splitBy/clocked zero    l        pivot = ret ([] , l)
  splitBy/clocked (suc k) []       pivot = ret ([] , [])
  splitBy/clocked (suc k) (x ∷ xs) pivot =
    bind (F pair) (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
      bind (F pair) (mid ≤ᵇ pivot) λ b →
        case b of
          λ { false → bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
            ; true  → bind (F pair) (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂) }

  splitBy/clocked/correct : ∀ k l pivot → ⌈log₂ suc (length l) ⌉ Nat.≤ k → Sorted l →
    ◯ (∃ λ l₁ → ∃ λ l₂ → splitBy/clocked k l pivot ≡ ret (l₁ , l₂) × All (_≤ pivot) l₁ × All (pivot ≤_) l₂ × l ≡ (l₁ ++ l₂))
  splitBy/clocked/correct zero    l        pivot h sorted u with ⌈log₂n⌉≡0⇒n≤1 {suc (length l)} (N.n≤0⇒n≡0 h)
  splitBy/clocked/correct zero    []       pivot h sorted u | s≤s z≤n = [] , [] , refl , [] , [] , refl
  splitBy/clocked/correct (suc k) []       pivot h sorted u = [] , [] , refl , [] , [] , refl
  splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) sorted u with splitMid/correct (x ∷ xs) (s≤s z≤n) u
  splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) sorted u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) with h-cost mid pivot
  splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) sorted u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ub/intro {q = q} b _ h-eq rewrite eq/ref h-eq
    with Eq.subst Sorted ≡-↭ sorted | ≤ᵇ-reflects-≤ u (Eq.trans (eq/ref h-eq) (step'/ext (F bool) (ret b) q u)) | ≤-total mid pivot
  splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) sorted u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ub/intro b     _ h-eq | sorted' | ofⁿ ¬p | inj₁ mid≤pivot = ⊥-elim (¬p mid≤pivot)
  splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) sorted u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ub/intro false _ h-eq | sorted' | ofⁿ ¬p | inj₂ pivot≤mid =
    let (l₁₁ , l₁₂ , ≡' , h₁₁ , h₁₂ , ≡-↭') = splitBy/clocked/correct k l₁ pivot (
                                                let open ≤-Reasoning in
                                                begin
                                                  ⌈log₂ suc (length l₁) ⌉
                                                ≤⟨ log₂-mono (s≤s h₁) ⟩
                                                  ⌈log₂ suc ⌊ length (x ∷ xs) /2⌋ ⌉
                                                ≤⟨ h ⟩
                                                  k
                                                ∎
                                              ) (++⁻ˡ l₁ sorted') u in
    l₁₁ , l₁₂ ++ mid ∷ l₂ , (
      let open ≡-Reasoning in
      begin
        splitBy/clocked (suc k) (x ∷ xs) pivot
      ≡⟨ {!   !} ⟩
        (bind (F pair) (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
          bind (F pair) (mid ≤ᵇ pivot) λ b →
            case b of
              λ { false → bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
                ; true  → bind (F pair) (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂) })
      ≡⟨
        {!   !}
        -- Eq.cong
        --   (λ e → bind (F pair) e (
        --       λ (l₁ , mid , l₂) →
        --         bind (F pair) (mid ≤ᵇ pivot) λ b →
        --           case b of
        --             λ { false → bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
        --               ; true  → bind (F pair) (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂) }
        --   ))
        --   ≡
      ⟩
        (bind (F pair) (ret {triple} (l₁ , mid , l₂)) λ (l₁ , mid , l₂) →
          bind (F pair) (mid ≤ᵇ pivot) λ b →
            case b of
              λ { false → bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
                ; true  → bind (F pair) (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂) })
      ≡⟨ {!   !} ⟩
        (bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂))
      ≡⟨ Eq.cong (λ e → bind (F pair) e _) ≡' ⟩
        ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
      ∎
    ) , h₁₁ , ++⁺-All h₁₂ (pivot≤mid ∷ ≤-≤* pivot≤mid (uncons₁ (++⁻ʳ l₁ sorted'))) , (
      let open ≡-Reasoning in
      begin
        (x ∷ xs)
      ≡⟨ ≡-↭ ⟩
        l₁ ++ mid ∷ l₂
      ≡⟨ Eq.cong (_++ (mid ∷ l₂)) ≡-↭' ⟩
        (l₁₁ ++ l₁₂) ++ mid ∷ l₂
      ≡⟨ ++-assoc l₁₁ l₁₂ (mid ∷ l₂) ⟩
        l₁₁ ++ (l₁₂ ++ mid ∷ l₂)
      ∎
    )
  splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) sorted u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ub/intro true  _ h-eq | sorted' | ofʸ p  | _              =
    let (l₂₁ , l₂₂ , ≡' , h₂₁ , h₂₂ , ≡-↭') = splitBy/clocked/correct k l₂ pivot (
                                                let open ≤-Reasoning in
                                                begin
                                                  ⌈log₂ suc (length l₂) ⌉
                                                ≤⟨ log₂-mono (s≤s h₂) ⟩
                                                  ⌈log₂ suc ⌊ length (x ∷ xs) /2⌋ ⌉
                                                ≤⟨ h ⟩
                                                  k
                                                ∎
                                              ) (uncons₂ (++⁻ʳ l₁ sorted')) u in
    l₁ ++ mid ∷ l₂₁ , l₂₂ , (
      let open ≡-Reasoning in
      {!   !}
    ) , ++⁺-All {xs = l₁} {ys = mid ∷ l₂₁} {!   !} (p ∷ h₂₁) , h₂₂ , (
      let open ≡-Reasoning in
      begin
        (x ∷ xs)
      ≡⟨ ≡-↭ ⟩
        l₁ ++ mid ∷ l₂
      ≡⟨ Eq.cong (λ l₂ → l₁ ++ mid ∷ l₂) ≡-↭' ⟩
        l₁ ++ mid ∷ (l₂₁ ++ l₂₂)
      ≡˘⟨ ++-assoc l₁ (mid ∷ l₂₁) l₂₂ ⟩
        (l₁ ++ mid ∷ l₂₁) ++ l₂₂
      ∎
    )

  splitBy/clocked/length : ∀ k l pivot → (κ : ℕ → ℕ → α) → ∃ λ n₁ → ∃ λ n₂ → n₁ Nat.≤ (length l) × n₂ Nat.≤ (length l) ×
    bind (meta α) (splitBy/clocked k l pivot) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ n₁ n₂
  splitBy/clocked/length zero    l        pivot κ = 0 , length l , z≤n , N.≤-refl , refl
  splitBy/clocked/length (suc k) []       pivot κ = 0 , 0 , z≤n , z≤n , refl
  splitBy/clocked/length (suc k) (x ∷ xs) pivot κ = {!   !}

  splitBy/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → Π A λ _ → cost)
  splitBy/clocked/cost zero    l        pivot = 𝟘
  splitBy/clocked/cost (suc k) []       pivot = 𝟘
  splitBy/clocked/cost (suc k) (x ∷ xs) pivot =
    bind cost (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) → splitMid/cost (x ∷ xs) (s≤s z≤n) ⊕
      bind cost (mid ≤ᵇ pivot) λ b → (1 , 1) ⊕
        (case b of
          λ { false → bind cost (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → splitBy/clocked/cost k l₁ pivot ⊕ 𝟘
            ; true  → bind cost (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/clocked/cost k l₂ pivot ⊕ 𝟘 })

  splitBy/clocked/cost/closed : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → Π A λ _ → cost)
  splitBy/clocked/cost/closed k _ _ = k , k

  splitBy/clocked/cost≤splitBy/clocked/cost/closed : ∀ k l pivot → splitBy/clocked/cost k l pivot P≤ splitBy/clocked/cost/closed k l pivot
  splitBy/clocked/cost≤splitBy/clocked/cost/closed zero    l        pivot = z≤n , z≤n
  splitBy/clocked/cost≤splitBy/clocked/cost/closed (suc k) []       pivot = z≤n , z≤n
  splitBy/clocked/cost≤splitBy/clocked/cost/closed (suc k) (x ∷ xs) pivot =
    begin
      splitBy/clocked/cost (suc k) (x ∷ xs) pivot
    ≤⟨ {!   !} ⟩
      splitBy/clocked/cost/closed (suc k) (x ∷ xs) pivot
    ∎
      where open P≤-Reasoning

  splitBy/clocked≤splitBy/clocked/cost : ∀ k l pivot → ub pair (splitBy/clocked k l pivot) (splitBy/clocked/cost k l pivot)
  splitBy/clocked≤splitBy/clocked/cost zero    l        pivot = ub/ret
  splitBy/clocked≤splitBy/clocked/cost (suc k) []       pivot = ub/ret
  splitBy/clocked≤splitBy/clocked/cost (suc k) (x ∷ xs) pivot =
    ub/bind {e = splitMid (x ∷ xs) (s≤s z≤n)} (splitMid/cost (x ∷ xs) (s≤s z≤n)) _ (splitMid≤splitMid/cost (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
      ub/bind (1 , 1) _ (h-cost mid pivot)
        λ { false → ub/bind (splitBy/clocked/cost k l₁ pivot) (λ _ → 𝟘) (splitBy/clocked≤splitBy/clocked/cost k l₁ pivot) λ _ → ub/ret
          ; true  → ub/bind (splitBy/clocked/cost k l₂ pivot) (λ _ → 𝟘) (splitBy/clocked≤splitBy/clocked/cost k l₂ pivot) λ _ → ub/ret }

  splitBy/clocked≤splitBy/clocked/cost/closed : ∀ k l pivot → ub pair (splitBy/clocked k l pivot) (splitBy/clocked/cost/closed k l pivot)
  splitBy/clocked≤splitBy/clocked/cost/closed k l pivot = ub/relax (splitBy/clocked/cost≤splitBy/clocked/cost/closed k l pivot) (splitBy/clocked≤splitBy/clocked/cost k l pivot)

  splitBy : cmp (Π (list A) λ _ → Π A λ _ → F pair)
  splitBy l pivot = splitBy/clocked ⌈log₂ suc (length l) ⌉ l pivot

  splitBy/correct : ∀ l pivot → Sorted l →
    ◯ (∃ λ l₁ → ∃ λ l₂ → splitBy l pivot ≡ ret (l₁ , l₂) × All (_≤ pivot) l₁ × All (pivot ≤_) l₂ × l ≡ (l₁ ++ l₂))
  splitBy/correct l pivot = splitBy/clocked/correct ⌈log₂ suc (length l) ⌉ l pivot N.≤-refl

  splitBy/length : ∀ l pivot (κ : ℕ → ℕ → α) → ∃ λ n₁ → ∃ λ n₂ → n₁ Nat.≤ (length l) × n₂ Nat.≤ (length l) ×
    bind (meta α) (splitBy l pivot) (λ (l₁ , l₂) → κ (length l₁) (length l₂)) ≡ κ n₁ n₂
  splitBy/length l pivot = splitBy/clocked/length ⌈log₂ suc (length l) ⌉ l pivot

  splitBy/cost : cmp (Π (list A) λ _ → Π A λ _ → cost)
  splitBy/cost l pivot = splitBy/clocked/cost ⌈log₂ suc (length l) ⌉ l pivot

  splitBy/cost/closed : cmp (Π (list A) λ _ → Π A λ _ → cost)
  splitBy/cost/closed l pivot = splitBy/clocked/cost/closed ⌈log₂ suc (length l) ⌉ l pivot

  splitBy≤splitBy/cost : ∀ l pivot → ub pair (splitBy l pivot) (splitBy/cost l pivot)
  splitBy≤splitBy/cost l pivot = splitBy/clocked≤splitBy/clocked/cost ⌈log₂ suc (length l) ⌉ l pivot

  splitBy≤splitBy/cost/closed : ∀ l pivot → ub pair (splitBy l pivot) (splitBy/cost/closed l pivot)
  splitBy≤splitBy/cost/closed l pivot = splitBy/clocked≤splitBy/clocked/cost/closed ⌈log₂ suc (length l) ⌉ l pivot

  merge/clocked : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → F (list A))
  merge/clocked zero    (l₁     , l₂) = ret (l₁ ++ l₂)
  merge/clocked (suc k) ([]     , l₂) = ret l₂
  merge/clocked (suc k) (x ∷ l₁ , l₂) =
    bind (F (list A)) (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) →
      bind (F (list A)) (splitBy l₂ pivot) λ (l₂₁ , l₂₂) →
        bind (F (list A)) (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') →
          ret (l₁' ++ pivot ∷ l₂')

  merge/clocked/correct : ∀ k l₁ l₂ → ⌈log₂ suc (length l₁) ⌉ Nat.≤ k → Sorted l₁ → Sorted l₂ →
    ◯ (∃ λ l → merge/clocked k (l₁ , l₂) ≡ ret l × SortedOf (l₁ ++ l₂) l)
  merge/clocked/correct zero    l₁       l₂ h-clock sorted₁ sorted₂ u with ⌈log₂n⌉≡0⇒n≤1 {suc (length l₁)} (N.n≤0⇒n≡0 h-clock)
  merge/clocked/correct zero    []       l₂ h-clock []      sorted₂ u | s≤s z≤n = l₂ , refl , refl , sorted₂
  merge/clocked/correct (suc k) []       l₂ h-clock []      sorted₂ u = l₂ , refl , refl , sorted₂
  merge/clocked/correct (suc k) (x ∷ l₁) l₂ h-clock sorted₁ sorted₂ u =
    let (l₁₁ , pivot , l₁₂ , ≡ , h₁₁ , h₁₂ , ≡-↭) = splitMid/correct (x ∷ l₁) (s≤s z≤n) u in
    let sorted₁ = Eq.subst Sorted ≡-↭ sorted₁ in
    let (l₂₁ , l₂₂ , ≡' , h₂₁ , h₂₂ , ≡-↭') = splitBy/correct l₂ pivot sorted₂ u in
    let sorted₂ = Eq.subst Sorted ≡-↭' sorted₂ in
    let (l₁' , ≡₁' , ↭₁' , sorted₁') = merge/clocked/correct k l₁₁ l₂₁
                                        (let open ≤-Reasoning in
                                        begin
                                          ⌈log₂ suc (length l₁₁) ⌉
                                        ≤⟨ log₂-mono (s≤s h₁₁) ⟩
                                          ⌈log₂ ⌈ suc (length (x ∷ l₁)) /2⌉ ⌉
                                        ≤⟨ log₂-suc (suc (length (x ∷ l₁))) h-clock ⟩
                                          k
                                        ∎)
                                        (++⁻ˡ l₁₁ sorted₁)
                                        (++⁻ˡ l₂₁ sorted₂)
                                        u in
    let (l₂' , ≡₂' , ↭₂' , sorted₂') = merge/clocked/correct k l₁₂ l₂₂
                                        (let open ≤-Reasoning in
                                        begin
                                          ⌈log₂ suc (length l₁₂) ⌉
                                        ≤⟨ log₂-mono (s≤s h₁₂) ⟩
                                          ⌈log₂ ⌈ suc (length (x ∷ l₁)) /2⌉ ⌉
                                        ≤⟨ log₂-suc (suc (length (x ∷ l₁))) h-clock ⟩
                                          k
                                        ∎)
                                        (uncons₂ (++⁻ʳ l₁₁ sorted₁))
                                        (++⁻ʳ l₂₁ sorted₂)
                                        u in
    l₁' ++ pivot ∷ l₂' , {!   !} , (
      let open PermutationReasoning in
      begin
        (x ∷ l₁) ++ l₂
      ≡⟨ Eq.cong₂ (_++_) ≡-↭ ≡-↭' ⟩
        (l₁₁ ++ pivot ∷ l₁₂) ++ (l₂₁ ++ l₂₂)
      ≡⟨ ++-assoc l₁₁ (pivot ∷ l₁₂) (l₂₁ ++ l₂₂) ⟩
        l₁₁ ++ (pivot ∷ l₁₂ ++ (l₂₁ ++ l₂₂))
      ↭⟨ ++⁺ˡ-↭ l₁₁ (++⁺ˡ-↭ (pivot ∷ l₁₂) (++-comm-↭ l₂₁ l₂₂)) ⟩
        l₁₁ ++ (pivot ∷ l₁₂ ++ (l₂₂ ++ l₂₁))
      ≡˘⟨ Eq.cong (l₁₁ ++_) (++-assoc (pivot ∷ l₁₂) l₂₂ l₂₁) ⟩
        l₁₁ ++ ((pivot ∷ l₁₂ ++ l₂₂) ++ l₂₁)
      ↭⟨ ++⁺ˡ-↭ l₁₁ (++-comm-↭ (pivot ∷ l₁₂ ++ l₂₂) l₂₁) ⟩
        l₁₁ ++ (l₂₁ ++ (pivot ∷ l₁₂ ++ l₂₂))
      ≡˘⟨ ++-assoc l₁₁ l₂₁ (pivot ∷ l₁₂ ++ l₂₂) ⟩
        (l₁₁ ++ l₂₁) ++ (pivot ∷ l₁₂ ++ l₂₂)
      ≡⟨⟩
        (l₁₁ ++ l₂₁) ++ pivot ∷ (l₁₂ ++ l₂₂)
      ↭⟨ ++⁺-↭ ↭₁' (prep pivot ↭₂') ⟩
        l₁' ++ pivot ∷ l₂'
      ∎
    ) , join-sorted sorted₁' sorted₂' (All-resp-↭ ↭₁' (++⁺-All {!   !} h₂₁)) (All-resp-↭ ↭₂' (++⁺-All {!   !} h₂₂))

  merge/clocked/length : ∀ k (l₁ l₂ : val (list A)) (κ : ℕ → α) →
    bind (meta α) (merge/clocked k (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  merge/clocked/length k l₁ l₂ κ = {!   !}

  merge/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → cost)
  merge/clocked/cost zero    (l₁     , l₂) = 𝟘
  merge/clocked/cost (suc k) ([]     , l₂) = 𝟘
  merge/clocked/cost (suc k) (x ∷ l₁ , l₂) =
    bind cost (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) → splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
      bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
        bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
          𝟘

  merge/clocked/cost/closed : cmp (Π (U (meta ℕ)) λ _ → Π pair λ _ → cost)
  merge/clocked/cost/closed k (l₁ , l₂) = pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉

  merge/clocked/cost≤merge/clocked/cost/closed : ∀ k p → merge/clocked/cost k p P≤ merge/clocked/cost/closed k p
  merge/clocked/cost≤merge/clocked/cost/closed zero    (l₁     , l₂) = z≤n , z≤n
  merge/clocked/cost≤merge/clocked/cost/closed (suc k) ([]     , l₂) = z≤n , z≤n
  merge/clocked/cost≤merge/clocked/cost/closed (suc k) (x ∷ l₁ , l₂) =
    let open P≤-Reasoning in
    begin
      (bind cost (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) → splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
        bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
          bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
            𝟘)
    ≤⟨
      Eq.subst id
        (Eq.sym (
          tbind/meta' triple ℂ ℂ (splitMid (x ∷ l₁) (s≤s z≤n))
            (λ (l₁₁ , pivot , l₁₂) → splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
              bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
                  𝟘)
            (λ (l₁₁ , pivot , l₁₂) →
              (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
                ((pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉) ⊗
                 (pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉)))
            _P≤_
        ))
        (dbind
          (λ (l₁₁ , pivot , l₁₂) → meta (
            (splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
              bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
                  𝟘)
            P≤
            ((⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
              ((pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉) ⊗
               (pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉)))
          ))
          (splitMid (x ∷ l₁) (s≤s z≤n))
          λ (l₁₁ , pivot , l₁₂) →
            let (n₂₁ , n₂₂ , h₁ , h₂ , ≡') = splitBy/length l₂ pivot λ n₂₁ n₂₂ →
                                              (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
                                                ((pred[2^ k ] * ⌈log₂ suc n₂₁ ⌉ , k * ⌈log₂ suc n₂₁ ⌉) ⊗
                                                 (pred[2^ k ] * ⌈log₂ suc n₂₂ ⌉ , k * ⌈log₂ suc n₂₂ ⌉)) in
            begin
              (splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
                bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                  bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
                    𝟘)
            ≡⟨ ⊕-identityˡ _ ⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
                  𝟘)
            ≡⟨
              Eq.cong (bind cost (splitBy l₂ pivot)) (funext λ (l₂₁ , l₂₂) → Eq.cong (splitBy/cost/closed l₂ pivot ⊕_) (
                Eq.cong (bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂))) (funext λ (l₁' , l₂') →
                  ⊕-identityʳ _
                )
              ))
            ⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                bind cost (merge/clocked k (l₁₁ , l₂₁) & merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') →
                  merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
            ≡⟨
              Eq.cong (bind cost (splitBy l₂ pivot)) (funext λ (l₂₁ , l₂₂) → Eq.cong (splitBy/cost/closed l₂ pivot ⊕_) (
                bind/par/seq
                  {e₁ = merge/clocked k (l₁₁ , l₂₁)}
                  {e₂ = merge/clocked k (l₁₂ , l₂₂)}
              ))
            ⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                bind cost (merge/clocked k (l₁₁ , l₂₁)) λ l₁' →
                  bind cost (merge/clocked k (l₁₂ , l₂₂)) λ l₂' →
                    merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
            ≡⟨
              Eq.cong (bind cost (splitBy l₂ pivot)) (funext λ (l₂₁ , l₂₂) → Eq.cong (splitBy/cost/closed l₂ pivot ⊕_) (
                Eq.cong (bind cost (merge/clocked k (l₁₁ , l₂₁))) (funext λ l₁' →
                  merge/clocked/length k l₁₂ l₂₂ _
                )
              ))
            ⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                bind cost (merge/clocked k (l₁₁ , l₂₁)) λ l₁' →
                  merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
            ≡⟨
              Eq.cong (bind cost (splitBy l₂ pivot)) (funext λ (l₂₁ , l₂₂) → Eq.cong (splitBy/cost/closed l₂ pivot ⊕_) (
                merge/clocked/length k l₁₁ l₂₁ _
              ))
            ⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
            ≤⟨
              Eq.subst id
                (Eq.sym (
                  tbind/meta' pair ℂ ℂ (splitBy l₂ pivot)
                    (λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                      merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
                    (λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                      merge/clocked/cost/closed k (l₁₁ , l₂₁) ⊗ merge/clocked/cost/closed k (l₁₂ , l₂₂))
                    _P≤_
                ))
                (dbind
                  (λ (l₂₁ , l₂₂) → meta (
                    (splitBy/cost/closed l₂ pivot ⊕
                      merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
                    P≤
                    (splitBy/cost/closed l₂ pivot ⊕
                      merge/clocked/cost/closed k (l₁₁ , l₂₁) ⊗ merge/clocked/cost/closed k (l₁₂ , l₂₂))
                  ))
                  (splitBy l₂ pivot)
                  λ (l₂₁ , l₂₂) → 
                    ⊕-monoʳ-≤ (splitBy/cost/closed l₂ pivot) (
                      ⊗-mono-≤
                        (merge/clocked/cost≤merge/clocked/cost/closed k (l₁₁ , l₂₁))
                        (merge/clocked/cost≤merge/clocked/cost/closed k (l₁₂ , l₂₂))
                    )
                )
            ⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
                merge/clocked/cost/closed k (l₁₁ , l₂₁) ⊗ merge/clocked/cost/closed k (l₁₂ , l₂₂))
            ≡⟨⟩
              (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
                ((pred[2^ k ] * ⌈log₂ suc (length l₂₁) ⌉ , k * ⌈log₂ suc (length l₂₁) ⌉) ⊗
                 (pred[2^ k ] * ⌈log₂ suc (length l₂₂) ⌉ , k * ⌈log₂ suc (length l₂₂) ⌉)))
            ≡⟨ ≡' ⟩
              (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
                ((pred[2^ k ] * ⌈log₂ suc n₂₁ ⌉ , k * ⌈log₂ suc n₂₁ ⌉) ⊗
                 (pred[2^ k ] * ⌈log₂ suc n₂₂ ⌉ , k * ⌈log₂ suc n₂₂ ⌉))
            ≤⟨
              ⊕-monoʳ-≤ ((⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉)) (
                ⊗-mono-≤ 
                  (N.*-monoʳ-≤ (pred[2^ k ]) (log₂-mono (s≤s h₁)) , N.*-monoʳ-≤ k (log₂-mono (s≤s h₁)))
                  (N.*-monoʳ-≤ (pred[2^ k ]) (log₂-mono (s≤s h₂)) , N.*-monoʳ-≤ k (log₂-mono (s≤s h₂)))
              )
            ⟩
              ((⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
                ((pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉) ⊗
                 (pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉)))
            ∎
        )
    ⟩
      (bind cost (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) →
        (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
          ((pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉) ⊗
           (pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉)))
    ≡⟨(
      let (_ , _ , _ , _ , ≡) = splitMid/length (x ∷ l₁) (s≤s z≤n) λ _ _ →
                                  (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
                                    ((pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉) ⊗
                                     (pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉)) in
      (≡)
    )⟩
      (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
        ((pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉) ⊗
         (pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉))
    ≡⟨ Eq.cong₂ _,_ (arithmetic/work ⌈log₂ suc (length l₂) ⌉) (arithmetic/span ⌈log₂ suc (length l₂) ⌉) ⟩
      pred[2^ suc k ] * ⌈log₂ suc (length l₂) ⌉ , suc k * ⌈log₂ suc (length l₂) ⌉
    ≡⟨⟩
      merge/clocked/cost/closed (suc k) (x ∷ l₁ , l₂)
    ∎
      where
        arithmetic/work : ∀ n → n + (pred[2^ k ] * n + pred[2^ k ] * n) ≡ pred[2^ suc k ] * n
        arithmetic/work n = 
          begin
            n + (pred[2^ k ] * n + pred[2^ k ] * n)
          ≡˘⟨ Eq.cong (n +_) (N.*-distribʳ-+ n (pred[2^ k ]) (pred[2^ k ])) ⟩
            n + (pred[2^ k ] + pred[2^ k ]) * n
          ≡˘⟨ Eq.cong (_+ (pred[2^ k ] + pred[2^ k ]) * n) (N.*-identityˡ n) ⟩
            1 * n + (pred[2^ k ] + pred[2^ k ]) * n
          ≡˘⟨ N.*-distribʳ-+ n 1 (pred[2^ k ] + pred[2^ k ]) ⟩
            suc (pred[2^ k ] + pred[2^ k ]) * n
          ≡⟨ Eq.cong (_* n) (pred[2^suc[n]] k) ⟩
            pred[2^ suc k ] * n
          ∎
            where open ≡-Reasoning

        arithmetic/span : ∀ n → n + (k * n ⊔ k * n) ≡ suc k * n
        arithmetic/span n =
          begin
            n + (k * n ⊔ k * n)
          ≡⟨ Eq.cong (n +_) (N.⊔-idem (k * n)) ⟩
            n + k * n
          ≡˘⟨ Eq.cong (_+ k * n) (N.*-identityˡ n) ⟩
            1 * n + k * n
          ≡˘⟨ N.*-distribʳ-+ n 1 k ⟩
            suc k * n
          ∎
            where open ≡-Reasoning

  merge/clocked≤merge/clocked/cost : ∀ k p → ub (list A) (merge/clocked k p) (merge/clocked/cost k p)
  merge/clocked≤merge/clocked/cost zero    (l₁     , l₂) = ub/ret
  merge/clocked≤merge/clocked/cost (suc k) ([]     , l₂) = ub/ret
  merge/clocked≤merge/clocked/cost (suc k) (x ∷ l₁ , l₂) =
    ub/bind (splitMid/cost (x ∷ l₁) (s≤s z≤n)) _ (splitMid≤splitMid/cost (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) →
      ub/bind (splitBy/cost/closed l₂ pivot) _ (splitBy≤splitBy/cost/closed l₂ pivot) λ (l₂₁ , l₂₂) →
        ub/bind (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) _ (ub/par (merge/clocked≤merge/clocked/cost k (l₁₁ , l₂₁)) (merge/clocked≤merge/clocked/cost k (l₁₂ , l₂₂))) λ (l₁' , l₂') →
          ub/ret

  merge/clocked≤merge/clocked/cost/closed : ∀ k p → ub (list A) (merge/clocked k p) (merge/clocked/cost/closed k p)
  merge/clocked≤merge/clocked/cost/closed k p = ub/relax (merge/clocked/cost≤merge/clocked/cost/closed k p) (merge/clocked≤merge/clocked/cost k p)

  merge : cmp (Π pair λ _ → F (list A))
  merge (l₁ , l₂) = merge/clocked ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

  merge/correct : ∀ l₁ l₂ → Sorted l₁ → Sorted l₂ →
    ◯ (∃ λ l → merge (l₁ , l₂) ≡ ret l × SortedOf (l₁ ++ l₂) l)
  merge/correct l₁ l₂ = merge/clocked/correct ⌈log₂ suc (length l₁) ⌉ l₁ l₂ N.≤-refl

  -- merge/length : ∀ l₁ l₂ (κ : ℕ → α) → bind (meta α) (merge (l₁ , l₂)) (κ ∘ length) ≡ κ (length l₁ + length l₂)
  -- merge/length l₁ l₂ = merge/clocked/length (length l₁ + length l₂) l₁ l₂

  merge/cost : cmp (Π pair λ _ → cost)
  merge/cost (l₁ , l₂) = merge/clocked/cost ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

  merge/cost/closed : cmp (Π pair λ _ → cost)
  merge/cost/closed (l₁ , l₂) = merge/clocked/cost/closed ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

  merge≤merge/cost : ∀ p → ub (list A) (merge p) (merge/cost p)
  merge≤merge/cost (l₁ , l₂) = merge/clocked≤merge/clocked/cost ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

  merge≤merge/cost/closed : ∀ p → ub (list A) (merge p) (merge/cost/closed p)
  merge≤merge/cost/closed (l₁ , l₂) = merge/clocked≤merge/clocked/cost/closed ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

  sort/clocked : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → F (list A))
  sort/clocked zero    l = ret l
  sort/clocked (suc k) l =
    bind (F (list A)) (split l) λ (l₁ , l₂) →
      bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge

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
    let (l' , ≡' , ↭' , sorted) = merge/correct l₁' l₂' sorted₁ sorted₂ u in
    l' , (
      let open ≡-Reasoning in
      begin
        sort/clocked (suc k) l
      ≡⟨⟩
        (bind (F (list A)) (split l) λ (l₁ , l₂) →
          bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge)
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
        bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge
      ≡⟨ Eq.cong (λ e → bind (F (list A)) e merge) (Eq.cong₂ _&_ ≡₁ ≡₂) ⟩
        bind (F (list A)) (ret l₁' & ret l₂') merge
      ≡⟨ bind/par 𝟘 𝟘 ⟩
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

  -- sort/clocked/length : ∀ k l (κ : ℕ → α) → bind (meta α) (sort/clocked k l) (κ ∘ length) ≡ κ (length l)
  -- sort/clocked/length {_} zero    l κ = refl
  -- sort/clocked/length {α} (suc k) l κ =
  --   begin
  --     bnd (sort/clocked (suc k) l) (κ ∘ length)
  --   ≡⟨⟩
  --     (bnd (split l) λ (l₁ , l₂) →
  --       bnd (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') →
  --         bnd (merge (l₁' , l₂')) (κ ∘ length))
  --   ≡⟨
  --     Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) →
  --       Eq.cong (bnd (sort/clocked k l₁ & sort/clocked k l₂)) (funext λ (l₁' , l₂') →
  --         merge/length l₁' l₂' κ
  --       )
  --     )
  --   ⟩
  --     (bnd (split l) λ (l₁ , l₂) →
  --       bnd (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') →
  --         κ (length l₁' + length l₂'))
  --   ≡⟨
  --     Eq.cong (bnd (split l)) (funext λ (l₁ , l₂) →
  --       {!   !}
  --     )
  --   ⟩
  --     (bnd (split l) λ (l₁ , l₂) →
  --       κ (length l₁ + length l₂))
  --   ≡⟨ split/length l (λ n₁ n₂ → κ (n₁ + n₂)) ⟩
  --     κ (⌊ length l /2⌋ + ⌈ length l /2⌉ )
  --   ≡⟨ Eq.cong κ (N.⌊n/2⌋+⌈n/2⌉≡n (length l)) ⟩
  --     κ (length l)
  --   ∎
  --   where
  --     open ≡-Reasoning

  --     bnd : ∀ {A} → cmp (F A) → (val A → α) → α
  --     bnd = bind (meta α)

  sort/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost zero    l = 𝟘
  sort/clocked/cost (suc k) l =
    bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
      bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂')

  sort/clocked/cost/closed : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
  sort/clocked/cost/closed k l = {!   !}

  sort/clocked/cost≤sort/clocked/cost/closed : ∀ k l → sort/clocked/cost k l P≤ sort/clocked/cost/closed k l
  sort/clocked/cost≤sort/clocked/cost/closed k l = {!   !}

  sort/clocked≤sort/clocked/cost : ∀ k l → ub (list A) (sort/clocked k l) (sort/clocked/cost k l)
  sort/clocked≤sort/clocked/cost zero    l = ub/ret
  sort/clocked≤sort/clocked/cost (suc k) l =
    ub/bind (split/cost l) _ (split≤split/cost l) λ (l₁ , l₂) →
      ub/bind (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) _ (ub/par (sort/clocked≤sort/clocked/cost k l₁) (sort/clocked≤sort/clocked/cost k l₂)) λ (l₁' , l₂') →
        merge≤merge/cost/closed (l₁' , l₂')

  sort/clocked≤sort/clocked/cost/closed : ∀ k l → ub (list A) (sort/clocked k l) (sort/clocked/cost/closed k l)
  sort/clocked≤sort/clocked/cost/closed k l = ub/relax (sort/clocked/cost≤sort/clocked/cost/closed k l) (sort/clocked≤sort/clocked/cost k l)

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

  sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
  sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

  sort≤sort/cost/closed : ∀ l → ub (list A) (sort l) (sort/cost/closed l)
  sort≤sort/cost/closed l = sort/clocked≤sort/clocked/cost/closed (sort/depth l) l

module Ex/MergeSortFast where
  module Sort = MergeSortFast NatComparable

  list' = list (U (meta ℕ))

  ex/split : cmp (F Sort.pair)
  ex/split = Sort.split (6 ∷ 2 ∷ 8 ∷ 3 ∷ 1 ∷ 8 ∷ 5 ∷ [])

  ex/splitMid : cmp (F Sort.triple)
  ex/splitMid = Sort.splitMid test/forward (s≤s z≤n)

  ex/splitBy : cmp (F Sort.pair)
  ex/splitBy = Sort.splitBy test/forward 5

  ex/merge : cmp (F list')
  ex/merge = Sort.merge (2 ∷ 3 ∷ 6 ∷ 8 ∷ [] , 1 ∷ 5 ∷ 8 ∷ [])

  ex/sort : cmp (F list')
  ex/sort = Sort.sort (1 ∷ 5 ∷ 3 ∷ 1 ∷ 2 ∷ [])

  ex/sort/forward : cmp (F list')
  ex/sort/forward = Sort.sort test/forward  -- cost: ?

  ex/sort/backward : cmp (F list')
  ex/sort/backward = Sort.sort test/backward  -- cost: ?

  ex/sort/shuffled : cmp (F list')
  ex/sort/shuffled = Sort.sort test/shuffled  -- cost: ?

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
