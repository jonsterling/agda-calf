{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.InsertionSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Nat.Square

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
insert/correct x (y ∷ ys) (h ∷ hs) u | ⇓ false withCost q [ _ , _ ] | ofⁿ ¬x≤y | inj₁ x≤y = contradiction x≤y ¬x≤y
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
insert/cost x []       = 𝟘
insert/cost x (y ∷ ys) with h-cost x y
... | ⇓ false withCost q [ q≤1 , h-eq ] = q ⊕ (insert/cost x ys ⊕ 𝟘)
... | ⇓ true  withCost q [ q≤1 , h-eq ] = q ⊕ 𝟘

insert/cost/closed : cmp (Π A λ _ → Π (list A) λ _ → cost)
insert/cost/closed x l = length l , length l

insert/cost≤insert/cost/closed : ∀ x l → ◯ (insert/cost x l ≤ₚ insert/cost/closed x l)
insert/cost≤insert/cost/closed x []       u = ≤ₚ-refl
insert/cost≤insert/cost/closed x (y ∷ ys) u with h-cost x y
... | ⇓ false withCost q [ q≤1 , h-eq ] =
  Eq.subst (λ n → (q ⊕ n) ≤ₚ (suc (length ys) , suc (length ys))) (Eq.sym (⊕-identityʳ (insert/cost x ys))) (
    ≤ₚ-trans
      (⊕-monoˡ-≤ _ (q≤1 u))
      (s≤s (proj₁ (insert/cost≤insert/cost/closed x ys u)) ,
        s≤s (proj₂ (insert/cost≤insert/cost/closed x ys u)))
  )
... | ⇓ true  withCost q [ q≤1 , h-eq ] =
  Eq.subst (_≤ₚ (suc (length ys) , suc (length ys))) (Eq.sym (⊕-identityʳ q)) (
    ≤ₚ-trans (q≤1 u) (s≤s z≤n , s≤s z≤n)
  )

insert≤insert/cost : ∀ x l → IsBounded (list A) (insert x l) (insert/cost x l)
insert≤insert/cost x []       = bound/ret
insert≤insert/cost x (y ∷ ys) with h-cost x y
... | ⇓ false withCost q [ q≤1 , h-eq ] rewrite eq/ref h-eq =
  bound/step q (insert/cost x ys ⊕ 𝟘) (bound/bind/const (insert/cost x ys) 𝟘 (insert≤insert/cost x ys) λ _ → bound/ret)
... | ⇓ true  withCost q [ q≤1 , h-eq ] rewrite eq/ref h-eq =
  bound/step q 𝟘 bound/ret

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
sort/cost []       = 𝟘
sort/cost (x ∷ xs) = bind cost (sort xs) (λ xs' → sort/cost xs ⊕ insert/cost/closed x xs')

sort/cost/closed : cmp (Π (list A) λ _ → cost)
sort/cost/closed l = length l  ² , length l  ²

sort/cost≤sort/cost/closed : ∀ l → ◯ (sort/cost l ≤ₚ sort/cost/closed l)
sort/cost≤sort/cost/closed []       u = ≤ₚ-refl
sort/cost≤sort/cost/closed (x ∷ xs) u =
  let (xs'   , h-xs'   , xs↭xs'     , sorted-xs'  ) = sort/correct xs u in
  let (x∷xs' , h-x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') = insert/correct x xs' sorted-xs' u in
  let open ≤ₚ-Reasoning in
  begin
    sort/cost (x ∷ xs)
  ≡⟨⟩
    bind cost (sort xs) (λ xs' → sort/cost xs ⊕ insert/cost/closed x xs')
  ≡⟨ Eq.cong (λ e → bind cost e λ xs' → sort/cost xs ⊕ insert/cost/closed x xs') h-xs' ⟩
    sort/cost xs ⊕ insert/cost/closed x xs'
  ≡⟨⟩
    sort/cost xs ⊕ (length xs' , length xs')
  ≡˘⟨ Eq.cong (sort/cost xs ⊕_) (Eq.cong₂ _,_ (↭-length xs↭xs') (↭-length xs↭xs')) ⟩
    sort/cost xs ⊕ (length xs , length xs)
  ≤⟨ ⊕-monoˡ-≤ (length xs , length xs) (sort/cost≤sort/cost/closed xs u) ⟩
    sort/cost/closed xs ⊕ (length xs , length xs)
  ≡⟨⟩
    (length xs  ² , length xs  ²) ⊕ (length xs , length xs)
  ≤⟨ lemma/arithmetic (length xs) , lemma/arithmetic (length xs) ⟩
    length (x ∷ xs)  ² , length (x ∷ xs)  ²
  ≡⟨⟩
    sort/cost/closed (x ∷ xs)
  ∎
    where
      lemma/arithmetic : ∀ n → n  ² + n Nat.≤ suc n  ²
      lemma/arithmetic n =
        begin
          n  ² + n
        ≡⟨ N.+-comm (n  ²) n ⟩
          n + n  ²
        ≡⟨⟩
          n + n * n
        ≤⟨ N.m≤n+m (n + n * n) (suc n) ⟩
          suc n + (n + n * n)
        ≡⟨⟩
          suc (n + (n + n * n))
        ≡˘⟨ Eq.cong (λ m → suc (n + m)) (N.*-suc n n) ⟩
          suc (n + n * suc n)
        ≡⟨⟩
          suc n  ²
        ∎
        where open ≤-Reasoning

sort≤sort/cost : ∀ l → IsBounded (list A) (sort l) (sort/cost l)
sort≤sort/cost []       = bound/ret
sort≤sort/cost (x ∷ xs) = bound/bind (sort/cost xs) (insert/cost/closed x) (sort≤sort/cost xs) (insert≤insert/cost/closed x)

sort≤sort/cost/closed : ∀ l → IsBounded (list A) (sort l) (sort/cost/closed l)
sort≤sort/cost/closed l = bound/relax (sort/cost≤sort/cost/closed l) (sort≤sort/cost l)

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n  ² , n  ²)
sort/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ l _ → sort≤sort/cost/closed l
