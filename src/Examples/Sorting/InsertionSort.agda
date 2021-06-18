{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Comparable

module Examples.Sorting.InsertionSort (M : Comparable) where

open import Calf
open import Calf.Types.Bool
open import Calf.Types.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)

private
  variable
    α : Set

open Comparable M
open import Examples.Sorting.Core M

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

sort≤sort/cost : ∀ l → ub (list A) (sort l) (sort/cost l)
sort≤sort/cost []       = ub/ret zero
sort≤sort/cost (x ∷ xs) =
  Eq.subst (ub _ _) (sort/length xs (_+_ (sort/cost xs))) (
    ub/bind (sort/cost xs) length (sort≤sort/cost xs) (insert≤insert/cost x)
  )

sort≤n² : ∀ l → ub (list A) (sort l) (length l ^ 2)
sort≤n² l = ub/relax (sort/cost≤n² l) (sort≤sort/cost l)
