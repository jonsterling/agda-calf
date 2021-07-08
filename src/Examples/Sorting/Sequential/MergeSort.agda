{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.MergeSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as N
open import Data.Nat.Square
open import Data.Nat.Log2


_≥_ : val A → val A → Set
x ≥ y = y ≤ x

_≰_ : val A → val A → Set
x ≰ y = ¬ x ≤ y

≰⇒≥ : _≰_ ⇒ _≥_
≰⇒≥ {x} {y} h with ≤-total x y
... | inj₁ h₁ = contradiction h₁ h
... | inj₂ h₂ = h₂

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

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n * ⌈log₂ n ⌉)
sort/asymptotic = 0 ≤n⇒f[n]≤g[n]via λ l _ →
  bound/relax
    (λ u → ≤-reflexive (N.*-comm ⌈log₂ length l ⌉ (length l)))
    (sort≤sort/cost/closed l)
