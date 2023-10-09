open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.MergeSortPar.Merge (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.Parallel parCostMonoid
open import Calf.Data.Bool
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.Equality
open import Calf.Data.IsBounded costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉; pred; _⊔_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Nat.Log2
open import Data.Nat.PredExp2


open import Examples.Sorting.Parallel.MergeSort.Split M


triple = Σ⁺ (list A) λ _ → Σ⁺ A λ _ → (list A)

splitMid/clocked : cmp (Π nat λ k → Π (list A) λ l → Π (U (meta (k Nat.< length l))) λ _ → F triple)
splitMid/clocked zero    (x ∷ xs) (s≤s h) = ret ([] , x , xs)
splitMid/clocked (suc k) (x ∷ xs) (s≤s h) =
  bind (F triple) (splitMid/clocked k xs h) λ (l₁ , mid , l₂) → ret ((x ∷ l₁) , mid , l₂)

splitMid/clocked/correct : ∀ k k' l h → k + suc k' ≡ length l →
  ◯ (∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → splitMid/clocked k l h ≡ ret (l₁ , mid , l₂) × length l₁ ≡ k × length l₂ ≡ k' × l ≡ (l₁ ++ [ mid ] ++ l₂))
splitMid/clocked/correct zero    k' (x ∷ xs) (s≤s h) refl     u = [] , x , xs , refl , refl , refl , refl
splitMid/clocked/correct (suc k) k' (x ∷ xs) (s≤s h) h-length u =
  let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct k k' xs h (N.suc-injective h-length) u in
  x ∷ l₁ , mid , l₂ , Eq.cong (λ e → bind (F triple) e λ (l₁ , mid , l₂) → ret ((x ∷ l₁) , mid , l₂)) ≡ , Eq.cong suc h₁ , h₂ , Eq.cong (x ∷_) ≡-↭

splitMid/clocked/cost : cmp (Π nat λ k → Π (list A) λ l → Π (U (meta (k Nat.< length l))) λ _ → cost)
splitMid/clocked/cost _ _ _ = 𝟘

splitMid/clocked≤splitMid/clocked/cost : ∀ k l h → IsBounded triple (splitMid/clocked k l h) (splitMid/clocked/cost k l h)
splitMid/clocked≤splitMid/clocked/cost zero    (x ∷ xs) (s≤s h) = bound/ret
splitMid/clocked≤splitMid/clocked/cost (suc k) (x ∷ xs) (s≤s h) =
  bound/bind/const 𝟘 𝟘 (splitMid/clocked≤splitMid/clocked/cost k xs h) λ (l₁ , mid , l₂) → bound/ret {a = (x ∷ l₁) , mid , l₂}

splitMid : cmp (Π (list A) λ l → Π (U (meta (0 Nat.< length l))) λ _ → F triple)
splitMid (x ∷ xs) (s≤s h) = splitMid/clocked ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)

splitMid/correct : ∀ l h →
  ◯ (∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → splitMid l h ≡ ret (l₁ , mid , l₂) × length l₁ Nat.≤ ⌊ length l /2⌋ × length l₂ Nat.≤ ⌊ length l /2⌋ × l ≡ (l₁ ++ [ mid ] ++ l₂))
splitMid/correct (x ∷ xs) (s≤s h) u =
  let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct ⌊ length (x ∷ xs) /2⌋ ⌊ pred (length (x ∷ xs)) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)
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

splitMid/cost : cmp (Π (list A) λ l → Π (U (meta (0 Nat.< length l))) λ _ → cost)
splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)

splitMid≤splitMid/cost : ∀ l h → IsBounded triple (splitMid l h) (splitMid/cost l h)
splitMid≤splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked≤splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)


splitBy/clocked : cmp (Π nat λ _ → Π (list A) λ _ → Π A λ _ → F pair)
splitBy/clocked/aux : cmp (Π nat λ _ → Π A λ _ → Π (list A) λ _ → Π A λ _ → Π (list A) λ _ → Π bool λ _ → F pair)

splitBy/clocked zero    l        pivot = ret ([] , l)
splitBy/clocked (suc k) []       pivot = ret ([] , [])
splitBy/clocked (suc k) (x ∷ xs) pivot =
  bind (F pair) (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
    bind (F pair) (mid ≤ᵇ pivot) (splitBy/clocked/aux k pivot l₁ mid l₂)

splitBy/clocked/aux k pivot l₁ mid l₂ false =
  bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
splitBy/clocked/aux k pivot l₁ mid l₂ true  =
  bind (F pair) (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂)

splitBy/clocked/correct : ∀ k l pivot → ⌈log₂ suc (length l) ⌉ Nat.≤ k →
  ◯ (∃ λ l₁ → ∃ λ l₂ → splitBy/clocked k l pivot ≡ ret (l₁ , l₂) × (Sorted l → All (_≤ pivot) l₁ × All (pivot ≤_) l₂) × l ≡ (l₁ ++ l₂))
splitBy/clocked/correct zero    l        pivot h u with ⌈log₂n⌉≡0⇒n≤1 {suc (length l)} (N.n≤0⇒n≡0 h)
splitBy/clocked/correct zero    []       pivot h u | s≤s z≤n = [] , [] , refl , (λ _ → [] , []) , refl
splitBy/clocked/correct (suc k) []       pivot h u = [] , [] , refl , (λ _ → [] , []) , refl
splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) u with splitMid/correct (x ∷ xs) (s≤s z≤n) u
splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) with h-cost mid pivot
splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ⇓ b withCost q [ _ , h-eq ]
  with ≤ᵇ-reflects-≤ u (Eq.trans (eq/ref h-eq) (step/ext (F bool) (ret b) q u)) | ≤-total mid pivot
splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ⇓ b     withCost q [ _ , h-eq ] | ofⁿ ¬p | inj₁ mid≤pivot = contradiction mid≤pivot ¬p
splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ⇓ false withCost q [ _ , h-eq ] | ofⁿ ¬p | inj₂ pivot≤mid =
  let (l₁₁ , l₁₂ , ≡' , h-sorted , ≡-↭') = splitBy/clocked/correct k l₁ pivot (
                                              let open ≤-Reasoning in
                                              begin
                                                ⌈log₂ suc (length l₁) ⌉
                                              ≤⟨ log₂-mono (s≤s h₁) ⟩
                                                ⌈log₂ suc ⌊ length (x ∷ xs) /2⌋ ⌉
                                              ≤⟨ h ⟩
                                                k
                                              ∎
                                            ) u in
  l₁₁ , l₁₂ ++ mid ∷ l₂ , (
    let open ≡-Reasoning in
    begin
      splitBy/clocked (suc k) (x ∷ xs) pivot
    ≡⟨⟩
      (bind (F pair) (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
        bind (F pair) (mid ≤ᵇ pivot) (splitBy/clocked/aux k pivot l₁ mid l₂))
    ≡⟨ Eq.cong (λ e → bind (F pair) e _) (≡) ⟩
      bind (F pair) (mid ≤ᵇ pivot) (splitBy/clocked/aux k pivot l₁ mid l₂)
    ≡⟨ Eq.cong (λ e → bind (F pair) e (splitBy/clocked/aux k pivot l₁ mid l₂)) (eq/ref h-eq) ⟩
      step (F pair) q (splitBy/clocked/aux k pivot l₁ mid l₂ false)
    ≡⟨ step/ext (F pair) (splitBy/clocked/aux k pivot l₁ mid l₂ false) q u ⟩
      splitBy/clocked/aux k pivot l₁ mid l₂ false
    ≡⟨⟩
      (bind (F pair) (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂))
    ≡⟨ Eq.cong (λ e → bind (F pair) e λ (l₁₁ , l₁₂) → ret (l₁₁ , l₁₂ ++ mid ∷ l₂)) ≡' ⟩
      ret (l₁₁ , l₁₂ ++ mid ∷ l₂)
    ∎
  ) , (
    λ sorted →
      let sorted' = Eq.subst Sorted ≡-↭ sorted in
      let (h₁₁ , h₁₂) = h-sorted (++⁻ˡ l₁ sorted') in
      h₁₁ , ++⁺-All h₁₂ (pivot≤mid ∷ ≤-≤* pivot≤mid (uncons₁ (++⁻ʳ l₁ sorted')))
  ) , (
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
splitBy/clocked/correct (suc k) (x ∷ xs) pivot (s≤s h) u | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) | ⇓ true withCost q [ _ , h-eq ] | ofʸ p  | _              =
  let (l₂₁ , l₂₂ , ≡' , h-sorted , ≡-↭') = splitBy/clocked/correct k l₂ pivot (
                                              let open ≤-Reasoning in
                                              begin
                                                ⌈log₂ suc (length l₂) ⌉
                                              ≤⟨ log₂-mono (s≤s h₂) ⟩
                                                ⌈log₂ suc ⌊ length (x ∷ xs) /2⌋ ⌉
                                              ≤⟨ h ⟩
                                                k
                                              ∎
                                            ) u in
  l₁ ++ mid ∷ l₂₁ , l₂₂ , (
    let open ≡-Reasoning in
    begin
      splitBy/clocked (suc k) (x ∷ xs) pivot
    ≡⟨⟩
      (bind (F pair) (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
        bind (F pair) (mid ≤ᵇ pivot) (splitBy/clocked/aux k pivot l₁ mid l₂))
    ≡⟨ Eq.cong (λ e → bind (F pair) e _) (≡) ⟩
      bind (F pair) (mid ≤ᵇ pivot) (splitBy/clocked/aux k pivot l₁ mid l₂)
    ≡⟨ Eq.cong (λ e → bind (F pair) e (splitBy/clocked/aux k pivot l₁ mid l₂)) (eq/ref h-eq) ⟩
      step (F pair) q (splitBy/clocked/aux k pivot l₁ mid l₂ true)
    ≡⟨ step/ext (F pair) (splitBy/clocked/aux k pivot l₁ mid l₂ true) q u ⟩
      splitBy/clocked/aux k pivot l₁ mid l₂ true
    ≡⟨⟩
      (bind (F pair) (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂))
    ≡⟨ Eq.cong (λ e → bind (F pair) e λ (l₂₁ , l₂₂) → ret (l₁ ++ mid ∷ l₂₁ , l₂₂)) ≡' ⟩
      ret (l₁ ++ mid ∷ l₂₁ , l₂₂)
    ∎
  ) , (
    λ sorted →
      let sorted' = Eq.subst Sorted ≡-↭ sorted in
      let (h₂₁ , h₂₂) = h-sorted (uncons₂ (++⁻ʳ l₁ sorted')) in
      ++⁺-All
        (map (λ h → ≤-trans h p) (split-sorted₁ l₁ (++⁻ˡ (l₁ ∷ʳ mid) (Eq.subst Sorted (Eq.sym (++-assoc l₁ [ mid ] l₂)) sorted'))))
        (p ∷ h₂₁) ,
      h₂₂
  ) , (
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

splitBy/clocked/cost : cmp (Π nat λ _ → Π (list A) λ _ → Π A λ _ → cost)
splitBy/clocked/cost/aux : cmp (Π nat λ _ → Π A λ _ → Π (list A) λ _ → Π A λ _ → Π (list A) λ _ → Π bool λ _ → cost)

splitBy/clocked/cost zero    l        pivot = 𝟘
splitBy/clocked/cost (suc k) []       pivot = 𝟘
splitBy/clocked/cost (suc k) (x ∷ xs) pivot =
  bind cost (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) → splitMid/cost (x ∷ xs) (s≤s z≤n) ⊕
    bind cost (mid ≤ᵇ pivot) λ b → (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b

splitBy/clocked/cost/aux k pivot l₁ mid l₂ false =
  bind cost (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → splitBy/clocked/cost k l₁ pivot ⊕ 𝟘
splitBy/clocked/cost/aux k pivot l₁ mid l₂ true  =
  bind cost (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/clocked/cost k l₂ pivot ⊕ 𝟘

splitBy/clocked/cost/closed : cmp (Π nat λ _ → Π (list A) λ _ → Π A λ _ → cost)
splitBy/clocked/cost/closed k _ _ = k , k

splitBy/clocked/cost≤splitBy/clocked/cost/closed : ∀ k l pivot → ⌈log₂ suc (length l) ⌉ Nat.≤ k →
  ◯ (splitBy/clocked/cost k l pivot ≤ₚ splitBy/clocked/cost/closed k l pivot)
splitBy/clocked/cost/aux≤k : ∀ k pivot l₁ mid l₂ b → ⌈log₂ suc (length l₁) ⌉ Nat.≤ k → ⌈log₂ suc (length l₂) ⌉ Nat.≤ k →
  ◯ (splitBy/clocked/cost/aux k pivot l₁ mid l₂ b ≤ₚ (k , k))

splitBy/clocked/cost≤splitBy/clocked/cost/closed zero    l        pivot h u = z≤n , z≤n
splitBy/clocked/cost≤splitBy/clocked/cost/closed (suc k) []       pivot h u = z≤n , z≤n
splitBy/clocked/cost≤splitBy/clocked/cost/closed (suc k) (x ∷ xs) pivot (s≤s h) u with splitMid/correct (x ∷ xs) (s≤s z≤n) u
... | (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) with h-cost mid pivot
... | ⇓ b withCost q [ _ , h-eq ] =
  begin
    splitBy/clocked/cost (suc k) (x ∷ xs) pivot
  ≡⟨⟩
    (bind cost (splitMid (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) → splitMid/cost (x ∷ xs) (s≤s z≤n) ⊕
      bind cost (mid ≤ᵇ pivot) λ b → (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b)
  ≡⟨ Eq.cong (λ e → bind cost e _) (≡) ⟩
    (splitMid/cost (x ∷ xs) (s≤s z≤n) ⊕
      bind cost (mid ≤ᵇ pivot) λ b → (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b)
  ≡⟨⟩
    (𝟘 ⊕
      bind cost (mid ≤ᵇ pivot) λ b → (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b)
  ≡⟨ ⊕-identityˡ _ ⟩
    (bind cost (mid ≤ᵇ pivot) λ b → (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b)
  ≡⟨ Eq.cong (λ e → bind cost e λ b → (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b) (eq/ref h-eq) ⟩
    step cost q ((1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b)
  ≡⟨ step/ext cost _ q u ⟩
    (1 , 1) ⊕ splitBy/clocked/cost/aux k pivot l₁ mid l₂ b
  ≤⟨
    ⊕-monoʳ-≤ (1 , 1) (
      splitBy/clocked/cost/aux≤k k pivot l₁ mid l₂ b
        (N.≤-trans (log₂-mono (s≤s h₁)) h)
        (N.≤-trans (log₂-mono (s≤s h₂)) h)
        u
    )
  ⟩
    (1 , 1) ⊕ (k , k)
  ≡⟨⟩
    (suc k , suc k)
  ≡⟨⟩
    splitBy/clocked/cost/closed (suc k) (x ∷ xs) pivot
  ∎
    where open ≤ₚ-Reasoning

splitBy/clocked/cost/aux≤k k pivot l₁ mid l₂ false h₁ h₂ u =
  let (l₁₁ , l₁₂ , ≡' , _ , ≡-↭') = splitBy/clocked/correct k l₁ pivot h₁ u in
  begin
    splitBy/clocked/cost/aux k pivot l₁ mid l₂ false
  ≡⟨⟩
    (bind cost (splitBy/clocked k l₁ pivot) λ (l₁₁ , l₁₂) → splitBy/clocked/cost k l₁ pivot ⊕ 𝟘)
  ≡⟨ Eq.cong (λ e → bind cost e λ (l₁₁ , l₁₂) → splitBy/clocked/cost k l₁ pivot ⊕ 𝟘) ≡' ⟩
    splitBy/clocked/cost k l₁ pivot ⊕ 𝟘
  ≡⟨ ⊕-identityʳ _ ⟩
    splitBy/clocked/cost k l₁ pivot
  ≤⟨ splitBy/clocked/cost≤splitBy/clocked/cost/closed k l₁ pivot h₁ u ⟩
    (k , k)
  ∎
    where open ≤ₚ-Reasoning
splitBy/clocked/cost/aux≤k k pivot l₁ mid l₂ true  h₁ h₂ u =
  let (l₂₁ , l₂₂ , ≡' , _ , ≡-↭') = splitBy/clocked/correct k l₂ pivot h₂ u in
  begin
    splitBy/clocked/cost/aux k pivot l₁ mid l₂ true
  ≡⟨⟩
    (bind cost (splitBy/clocked k l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/clocked/cost k l₂ pivot ⊕ 𝟘)
  ≡⟨ Eq.cong (λ e → bind cost e λ (l₂₁ , l₂₂) → splitBy/clocked/cost k l₂ pivot ⊕ 𝟘) ≡' ⟩
    splitBy/clocked/cost k l₂ pivot ⊕ 𝟘
  ≡⟨ ⊕-identityʳ _ ⟩
    splitBy/clocked/cost k l₂ pivot
  ≤⟨ splitBy/clocked/cost≤splitBy/clocked/cost/closed k l₂ pivot h₂ u ⟩
    (k , k)
  ∎
    where open ≤ₚ-Reasoning

splitBy/clocked≤splitBy/clocked/cost : ∀ k l pivot → IsBounded pair (splitBy/clocked k l pivot) (splitBy/clocked/cost k l pivot)
splitBy/clocked≤splitBy/clocked/cost zero    l        pivot = bound/ret
splitBy/clocked≤splitBy/clocked/cost (suc k) []       pivot = bound/ret
splitBy/clocked≤splitBy/clocked/cost (suc k) (x ∷ xs) pivot =
  bound/bind {e = splitMid (x ∷ xs) (s≤s z≤n)} (splitMid/cost (x ∷ xs) (s≤s z≤n)) _ (splitMid≤splitMid/cost (x ∷ xs) (s≤s z≤n)) λ (l₁ , mid , l₂) →
    bound/bind (1 , 1) _ (h-cost mid pivot)
      λ { false → bound/bind (splitBy/clocked/cost k l₁ pivot) (λ _ → 𝟘) (splitBy/clocked≤splitBy/clocked/cost k l₁ pivot) λ (l₁₁ , l₁₂) → bound/ret {a = l₁₁ , l₁₂ ++ mid ∷ l₂}
        ; true  → bound/bind (splitBy/clocked/cost k l₂ pivot) (λ _ → 𝟘) (splitBy/clocked≤splitBy/clocked/cost k l₂ pivot) λ (l₂₁ , l₂₂) → bound/ret {a = l₁ ++ mid ∷ l₂₁ , l₂₂} }

splitBy/clocked≤splitBy/clocked/cost/closed : ∀ k l pivot → ⌈log₂ suc (length l) ⌉ Nat.≤ k → IsBounded pair (splitBy/clocked k l pivot) (splitBy/clocked/cost/closed k l pivot)
splitBy/clocked≤splitBy/clocked/cost/closed k l pivot h = bound/relax (splitBy/clocked/cost≤splitBy/clocked/cost/closed k l pivot h) (splitBy/clocked≤splitBy/clocked/cost k l pivot)

splitBy : cmp (Π (list A) λ _ → Π A λ _ → F pair)
splitBy l pivot = splitBy/clocked ⌈log₂ suc (length l) ⌉ l pivot

splitBy/correct : ∀ l pivot →
  ◯ (∃ λ l₁ → ∃ λ l₂ → splitBy l pivot ≡ ret (l₁ , l₂) × (Sorted l → All (_≤ pivot) l₁ × All (pivot ≤_) l₂) × l ≡ (l₁ ++ l₂))
splitBy/correct l pivot = splitBy/clocked/correct ⌈log₂ suc (length l) ⌉ l pivot N.≤-refl

splitBy/cost : cmp (Π (list A) λ _ → Π A λ _ → cost)
splitBy/cost l pivot = splitBy/clocked/cost ⌈log₂ suc (length l) ⌉ l pivot

splitBy/cost/closed : cmp (Π (list A) λ _ → Π A λ _ → cost)
splitBy/cost/closed l pivot = splitBy/clocked/cost/closed ⌈log₂ suc (length l) ⌉ l pivot

splitBy≤splitBy/cost : ∀ l pivot → IsBounded pair (splitBy l pivot) (splitBy/cost l pivot)
splitBy≤splitBy/cost l pivot = splitBy/clocked≤splitBy/clocked/cost ⌈log₂ suc (length l) ⌉ l pivot

splitBy≤splitBy/cost/closed : ∀ l pivot → IsBounded pair (splitBy l pivot) (splitBy/cost/closed l pivot)
splitBy≤splitBy/cost/closed l pivot = splitBy/clocked≤splitBy/clocked/cost/closed ⌈log₂ suc (length l) ⌉ l pivot N.≤-refl


merge/clocked : cmp (Π nat λ _ → Π pair λ _ → F (list A))
merge/clocked zero    (l₁     , l₂) = ret (l₁ ++ l₂)
merge/clocked (suc k) ([]     , l₂) = ret l₂
merge/clocked (suc k) (x ∷ l₁ , l₂) =
  bind (F (list A)) (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) →
    bind (F (list A)) (splitBy l₂ pivot) λ (l₂₁ , l₂₂) →
      bind (F (list A)) (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') →
        ret (l₁' ++ pivot ∷ l₂')

merge/clocked/correct : ∀ k l₁ l₂ → ⌈log₂ suc (length l₁) ⌉ Nat.≤ k →
  ◯ (∃ λ l → merge/clocked k (l₁ , l₂) ≡ ret l × (Sorted l₁ → Sorted l₂ → SortedOf (l₁ ++ l₂) l))
merge/clocked/correct zero    l₁       l₂ h-clock u with ⌈log₂n⌉≡0⇒n≤1 {suc (length l₁)} (N.n≤0⇒n≡0 h-clock)
merge/clocked/correct zero    []       l₂ h-clock u | s≤s z≤n = l₂ , refl , (λ sorted₁ sorted₂ → refl , sorted₂)
merge/clocked/correct (suc k) []       l₂ h-clock u = l₂ , refl , (λ sorted₁ sorted₂ → refl , sorted₂)
merge/clocked/correct (suc k) (x ∷ l₁) l₂ h-clock u =
  let (l₁₁ , pivot , l₁₂ , ≡ , h₁₁ , h₁₂ , ≡-↭) = splitMid/correct (x ∷ l₁) (s≤s z≤n) u in
  let (l₂₁ , l₂₂ , ≡' , h-sorted₂ , ≡-↭') = splitBy/correct l₂ pivot u in
  let (l₁' , ≡₁' , h-sorted₁') = merge/clocked/correct k l₁₁ l₂₁
                                  (let open ≤-Reasoning in
                                  begin
                                    ⌈log₂ suc (length l₁₁) ⌉
                                  ≤⟨ log₂-mono (s≤s h₁₁) ⟩
                                    ⌈log₂ ⌈ suc (length (x ∷ l₁)) /2⌉ ⌉
                                  ≤⟨ log₂-suc (suc (length (x ∷ l₁))) h-clock ⟩
                                    k
                                  ∎)
                                  u in
  let (l₂' , ≡₂' , h-sorted₂') = merge/clocked/correct k l₁₂ l₂₂
                                  (let open ≤-Reasoning in
                                  begin
                                    ⌈log₂ suc (length l₁₂) ⌉
                                  ≤⟨ log₂-mono (s≤s h₁₂) ⟩
                                    ⌈log₂ ⌈ suc (length (x ∷ l₁)) /2⌉ ⌉
                                  ≤⟨ log₂-suc (suc (length (x ∷ l₁))) h-clock ⟩
                                    k
                                  ∎)
                                  u in
  l₁' ++ pivot ∷ l₂' , (
    let open ≡-Reasoning in
    begin
      merge/clocked (suc k) (x ∷ l₁ , l₂)
    ≡⟨⟩
      (bind (F (list A)) (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) →
        bind (F (list A)) (splitBy l₂ pivot) λ (l₂₁ , l₂₂) →
          bind (F (list A)) (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') →
            ret (l₁' ++ pivot ∷ l₂'))
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) (≡) ⟩
      (bind (F (list A)) (splitBy l₂ pivot) λ (l₂₁ , l₂₂) →
        bind (F (list A)) (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') →
          ret (l₁' ++ pivot ∷ l₂'))
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) (≡') ⟩
      (bind (F (list A)) (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') →
        ret (l₁' ++ pivot ∷ l₂'))
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) (Eq.cong₂ _∥_ ≡₁' ≡₂') ⟩
      ret (l₁' ++ pivot ∷ l₂')
    ∎
  ) ,
  λ sorted₁ sorted₂ →
    let (h₂₁ , h₂₂) = h-sorted₂ sorted₂ in
    let sorted₁ = Eq.subst Sorted ≡-↭  sorted₁
        sorted₂ = Eq.subst Sorted ≡-↭' sorted₂ in
    let (↭₁' , sorted₁') = h-sorted₁'          (++⁻ˡ l₁₁ sorted₁)  (++⁻ˡ l₂₁ sorted₂)
        (↭₂' , sorted₂') = h-sorted₂' (uncons₂ (++⁻ʳ l₁₁ sorted₁)) (++⁻ʳ l₂₁ sorted₂) in
    (
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
    ) ,
    join-sorted
      sorted₁'
      sorted₂'
      (All-resp-↭ ↭₁' (++⁺-All (split-sorted₁ l₁₁ (++⁻ˡ (l₁₁ ∷ʳ pivot) (Eq.subst Sorted (Eq.sym (++-assoc l₁₁ [ pivot ] l₁₂)) sorted₁))) h₂₁))
      (All-resp-↭ ↭₂' (++⁺-All (uncons₁ (++⁻ʳ l₁₁ sorted₁)) h₂₂))

merge/clocked/cost : cmp (Π nat λ _ → Π pair λ _ → cost)
merge/clocked/cost zero    (l₁     , l₂) = 𝟘
merge/clocked/cost (suc k) ([]     , l₂) = 𝟘
merge/clocked/cost (suc k) (x ∷ l₁ , l₂) =
  bind cost (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) → splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
    bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
      bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
        𝟘

merge/clocked/cost/closed : cmp (Π nat λ _ → Π pair λ _ → cost)
merge/clocked/cost/closed k (l₁ , l₂) = pred[2^ k ] * ⌈log₂ suc (length l₂) ⌉ , k * ⌈log₂ suc (length l₂) ⌉

merge/clocked/cost≤merge/clocked/cost/closed : ∀ k l₁ l₂ → ⌈log₂ suc (length l₁) ⌉ Nat.≤ k →
  ◯ (merge/clocked/cost k (l₁ , l₂) ≤ₚ merge/clocked/cost/closed k (l₁ , l₂))
merge/clocked/cost≤merge/clocked/cost/closed zero    l₁       l₂ h-clock u = z≤n , z≤n
merge/clocked/cost≤merge/clocked/cost/closed (suc k) []       l₂ h-clock u = z≤n , z≤n
merge/clocked/cost≤merge/clocked/cost/closed (suc k) (x ∷ l₁) l₂ h-clock u =
  let (l₁₁ , pivot , l₁₂ , ≡-splitMid , h₁₁ , h₁₂ , ≡-↭) = splitMid/correct (x ∷ l₁) (s≤s z≤n) u in
  let (l₂₁ , l₂₂ , ≡' , _ , ≡-↭') = splitBy/correct l₂ pivot u in
  let h₁ : ⌈log₂ suc (length l₁₁) ⌉ Nat.≤ k
      h₁ =
        let open ≤-Reasoning in
        begin
          ⌈log₂ suc (length l₁₁) ⌉
        ≤⟨ log₂-mono (s≤s h₁₁) ⟩
          ⌈log₂ ⌈ suc (length (x ∷ l₁)) /2⌉ ⌉
        ≤⟨ log₂-suc (suc (length (x ∷ l₁))) h-clock ⟩
          k
        ∎

      h₂ : ⌈log₂ suc (length l₁₂) ⌉ Nat.≤ k
      h₂ =
        let open ≤-Reasoning in
        begin
          ⌈log₂ suc (length l₁₂) ⌉
        ≤⟨ log₂-mono (s≤s h₁₂) ⟩
          ⌈log₂ ⌈ suc (length (x ∷ l₁)) /2⌉ ⌉
        ≤⟨ log₂-suc (suc (length (x ∷ l₁))) h-clock ⟩
          k
        ∎
  in
  let (l₁' , ≡₁' , _) = merge/clocked/correct k l₁₁ l₂₁ h₁ u in
  let (l₂' , ≡₂' , _) = merge/clocked/correct k l₁₂ l₂₂ h₂ u in
  let open ≤ₚ-Reasoning in
  begin
    (bind cost (splitMid (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) → splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
      bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
        bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
          𝟘)
  ≡⟨ Eq.cong (λ e → bind cost e λ (l₁₁ , pivot , l₁₂) → splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕ _) ≡-splitMid ⟩
    (splitMid/cost (x ∷ l₁) (s≤s z≤n) ⊕
      bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
        bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
          𝟘)
  ≡⟨⟩
    (𝟘 ⊕
      bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
        bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
          𝟘)
  ≡⟨ ⊕-identityˡ _ ⟩
    (bind cost (splitBy l₂ pivot) λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
      bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
        𝟘)
  ≡⟨
    Eq.cong
      (λ e →
        bind cost e λ (l₂₁ , l₂₂) → splitBy/cost/closed l₂ pivot ⊕
          bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
            𝟘)
      ≡'
  ⟩
    (splitBy/cost/closed l₂ pivot ⊕
      bind cost (merge/clocked k (l₁₁ , l₂₁) ∥ merge/clocked k (l₁₂ , l₂₂)) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
        𝟘)
  ≡⟨
    Eq.cong₂
      (λ e₁ e₂ →
        splitBy/cost/closed l₂ pivot ⊕
          bind cost (e₁ ∥ e₂) λ (l₁' , l₂') → (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕
            𝟘)
      ≡₁'
      ≡₂' ⟩
    splitBy/cost/closed l₂ pivot ⊕ ((merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) ⊕ 𝟘)
  ≡⟨ Eq.cong (splitBy/cost/closed l₂ pivot ⊕_) (⊕-identityʳ _) ⟩
    splitBy/cost/closed l₂ pivot ⊕ (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂))
  ≤⟨
    ⊕-monoʳ-≤ (splitBy/cost/closed l₂ pivot) (
      ⊗-mono-≤
        (merge/clocked/cost≤merge/clocked/cost/closed k l₁₁ l₂₁ h₁ u)
        (merge/clocked/cost≤merge/clocked/cost/closed k l₁₂ l₂₂ h₂ u)
    )
  ⟩
    splitBy/cost/closed l₂ pivot ⊕ (merge/clocked/cost/closed k (l₁₁ , l₂₁) ⊗ merge/clocked/cost/closed k (l₁₂ , l₂₂))
  ≡⟨⟩
    (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) ⊕
      ((pred[2^ k ] * ⌈log₂ suc (length l₂₁) ⌉ , k * ⌈log₂ suc (length l₂₁) ⌉) ⊗
        (pred[2^ k ] * ⌈log₂ suc (length l₂₂) ⌉ , k * ⌈log₂ suc (length l₂₂) ⌉))
  ≤⟨
    ⊕-monoʳ-≤ (⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₂) ⌉) (
      let h-length : length l₂₁ + length l₂₂ ≡ length l₂
          h-length = Eq.sym (Eq.trans (Eq.cong length ≡-↭') (length-++ l₂₁))

          h₁ : ⌈log₂ suc (length l₂₁) ⌉ Nat.≤ ⌈log₂ suc (length l₂) ⌉
          h₁ = log₂-mono (s≤s (N.m+n≤o⇒m≤o (length l₂₁) (N.≤-reflexive h-length)))

          h₂ : ⌈log₂ suc (length l₂₂) ⌉ Nat.≤ ⌈log₂ suc (length l₂) ⌉
          h₂ = log₂-mono (s≤s (N.m+n≤o⇒n≤o (length l₂₁) (N.≤-reflexive h-length)))
      in
      ⊗-mono-≤
        (N.*-monoʳ-≤ pred[2^ k ] h₁ , N.*-monoʳ-≤ k h₁)
        (N.*-monoʳ-≤ pred[2^ k ] h₂ , N.*-monoʳ-≤ k h₂)
    )
  ⟩
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
        ≡⟨⟩
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
        ≡⟨⟩
          suc k * n
        ∎
          where open ≡-Reasoning

merge/clocked≤merge/clocked/cost : ∀ k l₁ l₂ → IsBounded (list A) (merge/clocked k (l₁ , l₂)) (merge/clocked/cost k (l₁ , l₂))
merge/clocked≤merge/clocked/cost zero    l₁       l₂ = bound/ret
merge/clocked≤merge/clocked/cost (suc k) []       l₂ = bound/ret
merge/clocked≤merge/clocked/cost (suc k) (x ∷ l₁) l₂ =
  bound/bind (splitMid/cost (x ∷ l₁) (s≤s z≤n)) _ (splitMid≤splitMid/cost (x ∷ l₁) (s≤s z≤n)) λ (l₁₁ , pivot , l₁₂) →
    bound/bind (splitBy/cost/closed l₂ pivot) _ (splitBy≤splitBy/cost/closed l₂ pivot) λ (l₂₁ , l₂₂) →
      bound/bind (merge/clocked/cost k (l₁₁ , l₂₁) ⊗ merge/clocked/cost k (l₁₂ , l₂₂)) _ (bound/par (merge/clocked≤merge/clocked/cost k l₁₁ l₂₁) (merge/clocked≤merge/clocked/cost k l₁₂ l₂₂)) λ (l₁' , l₂') →
        bound/ret

merge/clocked≤merge/clocked/cost/closed : ∀ k l₁ l₂ → ⌈log₂ suc (length l₁) ⌉ Nat.≤ k →
  IsBounded (list A) (merge/clocked k (l₁ , l₂)) (merge/clocked/cost/closed k (l₁ , l₂))
merge/clocked≤merge/clocked/cost/closed k l₁ l₂ h =
  bound/relax (merge/clocked/cost≤merge/clocked/cost/closed k l₁ l₂ h) (merge/clocked≤merge/clocked/cost k l₁ l₂)

merge : cmp (Π pair λ _ → F (list A))
merge (l₁ , l₂) = merge/clocked ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

merge/correct : ∀ l₁ l₂ →
  ◯ (∃ λ l → merge (l₁ , l₂) ≡ ret l × (Sorted l₁ → Sorted l₂ → SortedOf (l₁ ++ l₂) l))
merge/correct l₁ l₂ = merge/clocked/correct ⌈log₂ suc (length l₁) ⌉ l₁ l₂ N.≤-refl

merge/cost : cmp (Π pair λ _ → cost)
merge/cost (l₁ , l₂) = merge/clocked/cost ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

merge/cost/closed : cmp (Π pair λ _ → cost)
merge/cost/closed (l₁ , l₂) = merge/clocked/cost/closed ⌈log₂ suc (length l₁) ⌉ (l₁ , l₂)

merge≤merge/cost : ∀ l₁ l₂ → IsBounded (list A) (merge (l₁ , l₂)) (merge/cost (l₁ , l₂))
merge≤merge/cost l₁ l₂ = merge/clocked≤merge/clocked/cost ⌈log₂ suc (length l₁) ⌉ l₁ l₂

merge≤merge/cost/closed : ∀ l₁ l₂ → IsBounded (list A) (merge (l₁ , l₂)) (merge/cost/closed (l₁ , l₂))
merge≤merge/cost/closed l₁ l₂ = merge/clocked≤merge/clocked/cost/closed ⌈log₂ suc (length l₁) ⌉ l₁ l₂ N.≤-refl
