{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.InsertionSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_)
import Data.Nat.Properties as N
open import Data.Nat.Square


insert : cmp (Π A λ _ → Π (list A) λ _ → F (list A))
insert x []       = ret [ x ]
insert x (y ∷ ys) =
  bind (F (list A)) (x ≤ᵇ y) λ b →
    if b
      then ret (x ∷ (y ∷ ys))
      else bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))

insert/correct : ∀ x l → Sorted l → ◯ (∃ λ l' → insert x l ≡ ret l' × SortedOf (x ∷ l) l')
insert/correct x []       []       u = [ x ] , refl , refl , [] ∷ []
insert/correct x (y ∷ ys) (h ∷ hs) u with x ≤? y
... | yes x≤y rewrite Equivalence.g (≤ᵇ-reflects-≤ u) (ofʸ x≤y) =
  x ∷ (y ∷ ys) , refl , refl , (x≤y ∷ ≤-≤* x≤y h) ∷ (h ∷ hs)
... | no ¬x≤y rewrite Equivalence.g (≤ᵇ-reflects-≤ u) (ofⁿ ¬x≤y) =
  let (ys' , h-ys' , x∷ys↭ys' , sorted-ys') = insert/correct x ys hs u in
  y ∷ ys' , Eq.cong (λ e → bind (F (list A)) e (ret ∘ (y ∷_))) h-ys' , (
    let open PermutationReasoning in
    begin
      x ∷ y ∷ ys
    <<⟨ refl ⟩
      y ∷ (x ∷ ys)
    <⟨ x∷ys↭ys' ⟩
      y ∷ ys'
    ∎
  ) , All-resp-↭ x∷ys↭ys' (≰⇒≥ ¬x≤y ∷ h) ∷ sorted-ys'

insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
insert/cost x l = length l

insert/is-bounded : ∀ x l → IsBounded (list A) (insert x l) (insert/cost x l)
insert/is-bounded x []       = bound/ret {list A} [ x ]
insert/is-bounded x (y ∷ ys) =
  bound/bind/const {bool} {list A}
    {x ≤ᵇ y}
    {λ b →
      if b
        then ret (x ∷ (y ∷ ys))
        else bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))}
    1
    (length ys)
    (h-cost x y)
    λ { false →
          Eq.subst
            (IsBounded (list A) (bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))))
            (+-identityʳ (length ys))
            (bound/bind/const {list A} {list A}
              {insert x ys}
              {ret ∘ (y ∷_)}
              (length ys)
              zero
              (insert/is-bounded x ys) λ ys' → bound/ret {list A} (y ∷ ys'))
      ; true  → bound/relax {list A} {ret (x ∷ (y ∷ ys))} (λ _ → z≤n {length ys}) (bound/ret {list A} (x ∷ (y ∷ ys))) }

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
sort/cost l = length l ²

sort/is-bounded : ∀ l → IsBounded (list A) (sort l) (sort/cost l)
sort/is-bounded []       = bound/ret {list A} []
sort/is-bounded (x ∷ xs) =
  Eq.subst
    (IsBounded (list A) (sort (x ∷ xs)))
    (N.+-comm (length xs * length (x ∷ xs)) (length (x ∷ xs)))
    ( bound/bind/const {list A} {list A} {sort xs} {insert x}
        (length xs * length (x ∷ xs))
        (length (x ∷ xs))
        (bound/relax {e = sort xs} (λ _ → N.*-monoʳ-≤ (length xs) (N.n≤1+n (length xs))) (sort/is-bounded xs))
        λ xs' →
          bound/relax
            {e = insert x xs'}
            (λ u →
              let open ≤-Reasoning in
              let (xs'' , sort-xs''≡ , ↭ , sorted) = sort/correct xs u in
              begin
                length xs'
              ≤⟨ N.n≤1+n (length xs') ⟩
                suc (length xs')
              ≡⟨ Eq.cong (suc ∘ length) {xs'} {xs''} {!   !} ⟩
                suc (length xs'')
              ≡˘⟨ Eq.cong suc (↭-length ↭) ⟩
                suc (length xs)
              ≡⟨⟩
                length (x ∷ xs)
              ∎)
            (insert/is-bounded x xs')
    )

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n ²)
sort/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ l _ → sort/is-bounded l
