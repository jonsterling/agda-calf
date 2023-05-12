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


η◯ : {A : tp pos} → val A → val (◯⁺ A)
η◯ a _ = a

Modal : (⋄ : tp pos → tp pos) (A : tp pos) → Set
Modal ⋄ A = val (⋄ A) ↔ val A

◯⁺-Modal : (A : tp pos) → Modal ◯⁺_ (◯⁺ A)
◯⁺-Modal A = record
  { to = λ x u → x u u
  ; from = λ x u _ → x u
  ; to-cong = λ h → funext/Ω λ u → Eq.cong (λ x → x u u) h
  ; from-cong = λ h → funext/Ω λ u → Eq.cong (λ x _ → x _) h
  ; inverse = (λ _ → refl) , (λ _ → refl)
  }

postulate
  lemma : (A : tp pos) (h : Modal ◯⁺_ A) (e : cmp (F A)) (v : val (◯⁺ A)) → ((u : ext) → e ≡ ret (v u)) →
    e ≡ bind (F A) e (λ _ → ret (Inverse.to h v))

lemma/◯⁺ : (A : tp pos) (e : cmp (F A)) (v : val (◯⁺ A)) → ((u : ext) → e ≡ ret (v u)) →
  (X : tp neg) (f : val (◯⁺ A) → cmp X) →
  bind X e (f ∘ η◯ {A}) ≡ bind X e (λ _ → f v)
lemma/◯⁺ A e v e≡ret[v] X f =
  Eq.cong
    (λ e → bind X e f)
    (lemma (◯⁺ A) (◯⁺-Modal A)
      (bind (F (◯⁺ A)) e (ret ∘ η◯ {A}))
      (η◯ {◯⁺ A} v)
      (λ u → Eq.cong (λ e → bind (F (◯⁺ A)) e (ret ∘ η◯ {A})) (e≡ret[v] u)))

open import Calf.Types.Unit
sort/is-bounded : ∀ l → IsBounded (list A) (sort l) (sort/cost l)
sort/is-bounded []       = bound/ret {list A} []
sort/is-bounded (x ∷ xs) =
  Eq.subst
    (IsBounded (list A) (sort (x ∷ xs)))
    (funext/Ω λ _ → N.+-comm (length xs * length (x ∷ xs)) (length (x ∷ xs)))
    λ result →
      let open ≲-Reasoning (F unit) in
      begin
        bind (F unit) (sort xs) (λ xs' → bind (F unit) (insert x xs') λ _ → result)
      ≤⟨ bind-mono-≲ (≲-refl {x = sort xs}) (λ xs' → insert/is-bounded x xs' result) ⟩
        bind (F unit) (sort xs) (λ xs' → step (F unit) (λ _ → length xs') result)
      ≡⟨ lemma/◯⁺ (list A) (sort xs) (λ u → proj₁ (sort/correct xs u)) (λ u → proj₁ (proj₂ (sort/correct xs u))) (F unit) (λ xs' → step (F unit) (λ u → length (xs' u)) result) ⟩
        bind (F unit) (sort xs) (λ _ → step (F unit) (λ u → length (proj₁ (sort/correct xs u))) result)
      ≤⟨ bind-mono-≲ (≲-refl {x = sort xs}) (λ _ → step-mono-≲ (λ u → N.≤-trans (N.≤-reflexive (Eq.sym (↭-length (proj₁ (proj₂ (proj₂ (sort/correct xs u))))))) (N.n≤1+n (length xs))) (≲-refl {x = result})) ⟩
        bind (F unit) (sort xs) (λ _ → step (F unit) (λ _ → length (x ∷ xs)) result)
      ≤⟨ sort/is-bounded xs (step (F unit) (λ _ → length (x ∷ xs)) result) ⟩
        step (F unit) (λ _ → length xs * length xs + length (x ∷ xs)) result
      ≤⟨ step-mono-≲ (λ _ → N.+-monoˡ-≤ (length (x ∷ xs)) (N.*-monoʳ-≤ (length xs) (N.n≤1+n (length xs)))) (≲-refl {x = result}) ⟩
        step (F unit) (λ _ → length xs * length (x ∷ xs) + length (x ∷ xs)) result
      ∎

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → λ _ → n ²)
sort/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ l _ → sort/is-bounded l
