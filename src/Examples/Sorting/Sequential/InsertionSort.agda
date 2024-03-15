{-# OPTIONS --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.InsertionSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid hiding (A)
open import Calf.Data.Bool using (bool)
open import Calf.Data.List
open import Calf.Data.Equality using (_≡_; refl)
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (∃)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_)
import Data.Nat.Properties as N
open import Data.Nat.Square


insert : cmp (Π A λ x → Π (list A) λ l → Π (sorted l) λ _ → F (Σ⁺ (list A) λ l' → sorted-of (x ∷ l) l'))
insert x []       []       = ret ([ x ] , refl , [] ∷ [])
insert x (y ∷ ys) (h ∷ hs) =
  bind (F _) (x ≤? y) $ case-≤
    (λ x≤y → ret (x ∷ (y ∷ ys) , refl , (x≤y ∷ ≤-≤* x≤y h) ∷ (h ∷ hs)))
    (λ x≰y →
      bind (F _) (insert x ys hs) λ (x∷ys' , x∷ys↭x∷ys' , sorted-x∷ys') →
      ret
        ( y ∷ x∷ys'
        , ( let open PermutationReasoning in
            begin
              x ∷ y ∷ ys
            <<⟨ refl ⟩
              y ∷ (x ∷ ys)
            <⟨ x∷ys↭x∷ys' ⟩
              y ∷ x∷ys'
            ∎
          )
        , All-resp-↭ x∷ys↭x∷ys' (≰⇒≥ x≰y ∷ h) ∷ sorted-x∷ys'
        ))

insert/total : ∀ x l h → IsValuable (insert x l h)
insert/total x []       []       u = ↓ refl
insert/total x (y ∷ ys) (h ∷ hs) u with ≤?-total x y u
... | yes x≤y , ≡ret rewrite ≡ret = ↓ refl
... | no x≰y , ≡ret rewrite ≡ret | Valuable.proof (insert/total x ys hs u) = ↓ refl

insert/cost : cmp (Π A λ _ → Π (list A) λ _ → cost)
insert/cost x l = step⋆ (length l)

insert/is-bounded : ∀ x l h → IsBoundedG (Σ⁺ (list A) λ l' → sorted-of (x ∷ l) l') (insert x l h) (insert/cost x l)
insert/is-bounded x []       []       = ≤⁻-refl
insert/is-bounded x (y ∷ ys) (h ∷ hs) =
  bound/bind/const {_} {Σ⁺ (list A) λ l' → sorted-of (x ∷ (y ∷ ys)) l'}
    {x ≤? y}
    {case-≤ _ _}
    1
    (length ys)
    (h-cost x y)
    λ { (yes x≤y) → step-monoˡ-≤⁻ (ret _) (z≤n {length ys})
      ; (no ¬x≤y) → insert/is-bounded x ys hs
      }


sort : cmp sorting
sort []       = ret ([] , refl , [])
sort (x ∷ xs) =
  bind (F (Σ⁺ (list A) (sorted-of (x ∷ xs)))) (sort xs) λ (xs' , xs↭xs' , sorted-xs') →
  bind (F (Σ⁺ (list A) (sorted-of (x ∷ xs)))) (insert x xs' sorted-xs') λ (x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') →
  ret (x∷xs' , trans (prep x xs↭xs') x∷xs↭x∷xs' , sorted-x∷xs')

sort/total : IsTotal sort
sort/total []       u = ↓ refl
sort/total (x ∷ xs) u = ↓
  let (xs' , xs↭xs' , sorted-xs') = Valuable.value (sort/total xs u) in
  let (x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') = Valuable.value (insert/total x xs' sorted-xs' u) in
  let open ≡-Reasoning in
  begin
    sort (x ∷ xs)
  ≡⟨
    Eq.cong
      (λ e →
        bind (F (Σ⁺ (list A) (sorted-of (x ∷ xs)))) e λ (xs' , xs↭xs' , sorted-xs') →
        bind (F (Σ⁺ (list A) (sorted-of (x ∷ xs)))) (insert x xs' sorted-xs') λ (x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') →
        ret (x∷xs' , trans (prep x xs↭xs') x∷xs↭x∷xs' , sorted-x∷xs'))
      (Valuable.proof (sort/total xs u))
  ⟩
    ( bind (F (Σ⁺ (list A) (sorted-of (x ∷ xs)))) (insert x xs' sorted-xs') λ (x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') →
      ret (x∷xs' , _ , sorted-x∷xs')
    )
  ≡⟨
    Eq.cong
      (λ e →
        bind (F (Σ⁺ (list A) (sorted-of (x ∷ xs)))) e λ (x∷xs' , x∷xs↭x∷xs' , sorted-x∷xs') →
        ret (x∷xs' , trans (prep x xs↭xs') x∷xs↭x∷xs' , sorted-x∷xs'))
      (Valuable.proof (insert/total x xs' sorted-xs' u))
  ⟩
    ret _
  ∎

sort/cost : cmp (Π (list A) λ _ → cost)
sort/cost l = step⋆ (length l ²)

sort/is-bounded : ∀ l → IsBoundedG (Σ⁺ (list A) (sorted-of l)) (sort l) (sort/cost l)
sort/is-bounded []       = ≤⁻-refl
sort/is-bounded (x ∷ xs) =
  let open ≤⁻-Reasoning cost in
  begin
    ( bind cost (sort xs) λ (xs' , xs↭xs' , sorted-xs') →
      bind cost (insert x xs' sorted-xs') λ _ →
      step⋆ zero
    )
  ≤⁻⟨ bind-monoʳ-≤⁻ (sort xs) (λ (xs' , xs↭xs' , sorted-xs') → insert/is-bounded x xs' sorted-xs') ⟩
    ( bind cost (sort xs) λ (xs' , xs↭xs' , sorted-xs') →
      step⋆ (length xs')
    )
  ≡˘⟨
    Eq.cong
      (bind cost (sort xs))
      (funext λ (xs' , xs↭xs' , sorted-xs') → Eq.cong step⋆ (↭-length xs↭xs'))
  ⟩
    ( bind cost (sort xs) λ _ →
      step⋆ (length xs)
    )
  ≤⁻⟨ bind-monoˡ-≤⁻ (λ _ → step⋆ (length xs)) (sort/is-bounded xs) ⟩
    step⋆ ((length xs ²) + length xs)
  ≤⁻⟨ step⋆-mono-≤⁻ (N.+-mono-≤ (N.*-monoʳ-≤ (length xs) (N.n≤1+n (length xs))) (N.n≤1+n (length xs))) ⟩
    step⋆ (length xs * length (x ∷ xs) + length (x ∷ xs))
  ≡⟨ Eq.cong step⋆ (N.+-comm (length xs * length (x ∷ xs)) (length (x ∷ xs))) ⟩
    step⋆ (length (x ∷ xs) ²)
  ≡⟨⟩
    sort/cost (x ∷ xs)
  ∎

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n ²)
sort/asymptotic = f[n]≤g[n]via sort/is-bounded
