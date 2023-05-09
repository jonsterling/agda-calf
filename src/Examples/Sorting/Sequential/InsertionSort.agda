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
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
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
... | yes x≤y rewrite Equivalence.from (≤ᵇ-reflects-≤ u) (ofʸ x≤y) =
  x ∷ (y ∷ ys) , refl , refl , (x≤y ∷ ≤-≤* x≤y h) ∷ (h ∷ hs)
... | no ¬x≤y rewrite Equivalence.from (≤ᵇ-reflects-≤ u) (ofⁿ ¬x≤y) =
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

insert/cost : cmp (Π A λ _ → Π (list A) λ _ → meta ℂ)
insert/cost x l = λ _ → length l

insert/is-bounded : ∀ x l → IsBounded (list A) (insert x l) (insert/cost x l)
insert/is-bounded x []       = bound/ret {list A} [ x ]
insert/is-bounded x (y ∷ ys) =
  bound/bind/const {bool} {list A}
    {x ≤ᵇ y}
    {λ b →
      if b
        then ret (x ∷ (y ∷ ys))
        else bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))}
    (λ _ → 1)
    (λ _ → length ys)
    (h-cost x y)
    λ { false →
          Eq.subst
            (IsBounded (list A) (bind (F (list A)) (insert x ys) (ret ∘ (y ∷_))))
            (+-identityʳ (λ _ → length ys))
            (bound/bind/const {list A} {list A}
              {insert x ys}
              {ret ∘ (y ∷_)}
              (λ _ → length ys)
              (λ _ → zero)
              (insert/is-bounded x ys) λ ys' → bound/ret {list A} (y ∷ ys'))
      ; true  → bound/relax (λ _ → z≤n {length ys}) {list A} {ret (x ∷ (y ∷ ys))} (bound/ret {list A} (x ∷ (y ∷ ys)))
      }

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

sort/cost : cmp (Π (list A) λ _ → meta ℂ)
sort/cost l = λ _ → length l ²

Modal : (⋄ : tp pos → tp pos) (A : tp pos) → Set
Modal ⋄ A = val (⋄ A) ↔ val A

postulate
  lemma : (A : tp pos) (h : Modal ◯⁺_ A) (e : cmp (F A)) (v : ext → val A) → ((u : ext) → e ≡ ret (v u)) →
    (X : tp neg) (f : val A → cmp X) →
    bind X e f ≡ bind X e (const (f (Inverse.to h v)))

  lemma' : (A : tp pos) (h : Modal ◯⁺_ A) {e : ◯ (val A)} (u : ext) → Inverse.to h e ≡ e u

  list-modal : Modal ◯⁺_ (list A)

sort/is-bounded : ∀ l → IsBounded (list A) (sort l) (sort/cost l)
sort/is-bounded []       = bound/ret {list A} []
sort/is-bounded (x ∷ xs) =
  let
    xs' : val (list A)
    xs' = Inverse.to list-modal (λ u → proj₁ (sort/correct xs u))
  in
  Eq.subst₂
    (IsBounded (list A))
    {x = bind (F (list A)) (sort xs) (λ _ → insert x xs')}
    {y = sort (x ∷ xs)}
    ( Eq.sym $
      lemma (list A) list-modal
        (sort xs)
        (λ u → proj₁ (sort/correct xs u))
        (λ u → proj₁ (proj₂ (sort/correct xs u)))
        (F (list A))
        (insert x)
    )
    (funext/Ω λ _ → N.+-comm (length xs * length (x ∷ xs)) (length (x ∷ xs)))
    ( bound/bind/const {list A} {list A} {sort xs} {λ _ → insert x xs'}
        (λ _ → length xs * length (x ∷ xs))
        (λ _ → length (x ∷ xs))
        (bound/relax (λ _ → N.*-monoʳ-≤ (length xs) (N.n≤1+n (length xs))) {e = sort xs} (sort/is-bounded xs))
        λ _ →
          bound/relax
            {c = λ _ → length xs'}
            {c' = λ _ → length (x ∷ xs)}
            ( let open ≤-Reasoning in
              begin
                (λ _ → length xs')
              ≤⟨ (λ _ → N.n≤1+n (length xs')) ⟩
                (λ _ → suc (length xs'))
              ≡⟨ (funext/Ω λ u → Eq.cong (suc ∘ length) (lemma' (list A) list-modal u)) ⟩
                (λ u → suc (length (proj₁ (sort/correct xs u))))
              ≡˘⟨ (funext/Ω λ u → Eq.cong suc (↭-length (proj₁ (proj₂ (proj₂ (sort/correct xs u)))))) ⟩
                (λ _ → suc (length xs))
              ≡⟨⟩
                (λ _ → length (x ∷ xs))
              ∎
            )
            {e = insert x xs'}
            (insert/is-bounded x xs')
    )

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → λ _ → n ²)
sort/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ l _ → sort/is-bounded l
