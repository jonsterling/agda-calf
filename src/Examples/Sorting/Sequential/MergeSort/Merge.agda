open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.MergeSort.Merge (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_)
import Data.Nat.Properties as N


open import Examples.Sorting.Sequential.MergeSort.Split M

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
    ≡⟨ step/ext (F (list A)) (bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_))) q u ⟩
      bind (F (list A)) (merge/clocked k (x ∷ xs , ys)) (ret ∘ (y ∷_))
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e (ret ∘ (y ∷_))) ≡ ⟩
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
        ↭⟨ ++-comm-↭ (x ∷ xs) (y ∷ ys) ⟩
          (y ∷ ys ++ x ∷ xs)
        ≡⟨⟩
          y ∷ (ys ++ x ∷ xs)
        <⟨ ++-comm-↭ ys (x ∷ xs) ⟩
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
    ≡⟨ step/ext (F (list A)) (bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_))) q u ⟩
      bind (F (list A)) (merge/clocked k (xs , y ∷ ys)) (ret ∘ (x ∷_))
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e (ret ∘ (x ∷_))) ≡ ⟩
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
merge/clocked≤merge/clocked/cost (suc k) ([]     , l₂    ) = bound/ret
merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , []    ) = bound/ret
merge/clocked≤merge/clocked/cost (suc k) (x ∷ xs , y ∷ ys) =
  bound/bind 1 _ (h-cost x y) λ b →
    bound/bool {p = λ b → if_then_else_ b _ _} b
      (bound/bind (merge/clocked/cost k (x ∷ xs , ys)) _ (merge/clocked≤merge/clocked/cost k (x ∷ xs , ys)) λ l → bound/ret {a = y ∷ l})
      (bound/bind (merge/clocked/cost k (xs , y ∷ ys)) _ (merge/clocked≤merge/clocked/cost k (xs , y ∷ ys)) λ l → bound/ret {a = x ∷ l})

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
