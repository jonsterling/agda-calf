{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Comparable

module Examples.Sorting.MergeSort (M : Comparable) where

open import Calf
open import Calf.Types.Bool
open import Calf.Types.List as List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Properties as N using (module ≤-Reasoning)

private
  variable
    α : Set

open Comparable M
open import Examples.Sorting.Core M
open Extras M

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

sort/recurrence≡kn : ∀ k n → sort/recurrence k n ≡ k * n
sort/recurrence≡kn zero    n = refl
sort/recurrence≡kn (suc k) n =
  begin
    sort/recurrence (suc k) n
  ≡⟨⟩
    sort/recurrence k ⌊ n /2⌋ + sort/recurrence k ⌈ n /2⌉ + n
  ≡⟨
    Eq.cong (_+ n) (
      Eq.cong₂ _+_
        (sort/recurrence≡kn k ⌊ n /2⌋)
        (sort/recurrence≡kn k ⌈ n /2⌉)
    )
  ⟩
    k * ⌊ n /2⌋ + k * ⌈ n /2⌉ + n
  ≡˘⟨ Eq.cong (_+ n) (N.*-distribˡ-+ k ⌊ n /2⌋ ⌈ n /2⌉) ⟩
    k * (⌊ n /2⌋ + ⌈ n /2⌉) + n
  ≡⟨ Eq.cong (λ n' → k * n' + n) (N.⌊n/2⌋+⌈n/2⌉≡n n) ⟩
    k * n + n
  ≡⟨ N.+-comm (k * n) n ⟩
    n + k * n
  ≡⟨⟩
    suc k * n
  ∎
    where open ≡-Reasoning

sort/clocked/cost : cmp (Π (U (meta ℕ)) λ _ → Π (list A) λ _ → cost)
sort/clocked/cost k l = sort/recurrence k (length l)

sort/clocked/cost=kn : ∀ k l → sort/clocked/cost k l ≡ k * length l
sort/clocked/cost=kn k l = sort/recurrence≡kn k (length l)

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

sort/clocked≤kn : ∀ k l → ub (list A) (sort/clocked k l) (k * length l)
sort/clocked≤kn k l = Eq.subst (ub _ _) (sort/clocked/cost=kn k l) (sort/clocked≤sort/clocked/cost k l)

sort/depth : cmp (Π (list A) λ _ → meta ℕ)
sort/depth l = ⌈log₂ length l ⌉

sort : cmp (Π (list A) λ _ → F (list A))
sort l = sort/clocked (sort/depth l) l

sort/correct : IsSort sort
sort/correct l = sort/clocked/correct (sort/depth l) l N.≤-refl

sort/cost : cmp (Π (list A) λ _ → cost)
sort/cost l = sort/clocked/cost (sort/depth l) l

sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
sort≤sort/cost l = sort/clocked≤sort/clocked/cost (sort/depth l) l

sort≤nlog₂n : ∀ l → ub (list A) (sort l) (length l * ⌈log₂ length l ⌉)
sort≤nlog₂n l = Eq.subst (ub _ _) (N.*-comm _ (length l)) (sort/clocked≤kn (sort/depth l) l)
