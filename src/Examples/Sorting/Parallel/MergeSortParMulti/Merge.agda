{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.MergeSortParMulti.Merge (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid

open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat as N using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉; pred; _⊔_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Nat.Log2
open import Data.Nat.PredExp2

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All

open import Examples.Sorting.Parallel.MergeSort.Split M


triple = Σ++ (list A) λ _ → Σ++ A λ _ → (list A)

splitMid/clocked : cmp (Π nat λ k → Π (list A) λ l → Π (U (meta (k N.< length l))) λ _ → F triple)
splitMid/clocked zero    (x ∷ xs) (s≤s h) = ret ([] , x , xs)
splitMid/clocked (suc k) (x ∷ xs) (s≤s h) =
  bind (F triple) (splitMid/clocked k xs h) λ (l₁ , mid , l₂) → ret ((x ∷ l₁) , mid , l₂)

splitMid/clocked/correct : ∀ k k' l h → k + suc k' ≡ length l →
  ∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → ◯ (splitMid/clocked k l h ≡ ret (l₁ , mid , l₂)) × length l₁ ≡ k × length l₂ ≡ k' × l ≡ (l₁ ++ [ mid ] ++ l₂)
splitMid/clocked/correct zero    k' (x ∷ xs) (s≤s h) refl     = [] , x , xs , (λ u → refl) , refl , refl , refl
splitMid/clocked/correct (suc k) k' (x ∷ xs) (s≤s h) h-length =
  let (l₁ , mid , l₂ , ≡ , h₁ , h₂ , ≡-↭) = splitMid/clocked/correct k k' xs h (N.suc-injective h-length) in
  x ∷ l₁ , mid , l₂ , (λ u → Eq.cong (λ e → bind (F triple) e _) (≡ u)) , Eq.cong suc h₁ , h₂ , Eq.cong (x ∷_) ≡-↭

splitMid/clocked/cost : cmp (Π nat λ k → Π (list A) λ l → Π (U (meta (k N.< length l))) λ _ → cost)
splitMid/clocked/cost _ _ _ = 𝟘

splitMid/clocked≤splitMid/clocked/cost : ∀ k l h → IsBounded triple (splitMid/clocked k l h) (splitMid/clocked/cost k l h)
splitMid/clocked≤splitMid/clocked/cost zero    (x ∷ xs) (s≤s h) = bound/ret
splitMid/clocked≤splitMid/clocked/cost (suc k) (x ∷ xs) (s≤s h) =
  bound/bind/const 𝟘 𝟘 (splitMid/clocked≤splitMid/clocked/cost k xs h) λ _ → bound/ret

splitMid : cmp (Π (list A) λ l → Π (U (meta (0 N.< length l))) λ _ → F triple)
splitMid (x ∷ xs) (s≤s h) = splitMid/clocked ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)

splitMid/correct : ∀ l h →
  ∃ λ l₁ → ∃ λ mid → ∃ λ l₂ → ◯ (splitMid l h ≡ ret (l₁ , mid , l₂)) × length l₁ N.≤ ⌊ length l /2⌋ × length l₂ N.≤ ⌊ length l /2⌋ × l ≡ (l₁ ++ [ mid ] ++ l₂)
splitMid/correct (x ∷ xs) (s≤s h) =
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
                                              ∎) in
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

splitMid/cost : cmp (Π (list A) λ l → Π (U (meta (0 N.< length l))) λ _ → cost)
splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)

splitMid≤splitMid/cost : ∀ l h → IsBounded triple (splitMid l h) (splitMid/cost l h)
splitMid≤splitMid/cost (x ∷ xs) (s≤s h) = splitMid/clocked≤splitMid/clocked/cost ⌊ length (x ∷ xs) /2⌋ (x ∷ xs) (N.⌊n/2⌋<n _)


pairs = Σ++ pair λ _ → pair

bisplit/clocked : cmp (Π nat λ _ → Π pair λ (a , b) → Π nat λ n → Π (U (meta (n N.≤ length a + length b))) λ _ → F pairs)
bisplit/clocked zero    (a      , b     ) n h = ret ((a , []) , (b , []))
bisplit/clocked (suc k) ([]     , b     ) n h = bind (F pairs) (split/clocked n b       ) λ bp → ret (([] , []) , bp)
bisplit/clocked (suc k) (a ∷ as , []    ) n h = bind (F pairs) (split/clocked n (a ∷ as)) λ ap → ret (ap , ([] , []))
bisplit/clocked (suc k) (a ∷ as , b ∷ bs) n h =
  bind (F pairs) (splitMid (a ∷ as) (s≤s z≤n)) λ (a₁ , aMid , a₂) →
    bind (F pairs) (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) →
      bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
        if n N.≤ᵇ length a₁ + length b₁
          then
            if condition
              then
                (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
              else
                (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
          else
            if condition
              then
                (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as))) {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
              else
                (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs))) {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂')))

record NSplitters (p : val pair) (n : val nat) (splitters : val pairs) : Set where
  private
    a = proj₁ p
    b = proj₂ p

    a₁ = proj₁ (proj₁ splitters)
    a₂ = proj₂ (proj₁ splitters)
    b₁ = proj₁ (proj₂ splitters)
    b₂ = proj₂ (proj₂ splitters)

  field
    proof-a : a ≡ a₁ ++ a₂
    proof-b : b ≡ b₁ ++ b₂
    proof-align₁ : All (λ aᵢ → All (λ bⱼ → aᵢ ≤ bⱼ) b₂) a₁
    proof-align₂ : All (λ bᵢ → All (λ aⱼ → bᵢ ≤ aⱼ) a₂) b₁
    proof-n : length a₁ + length b₁ ≡ n

bisplit/clocked/correct : ∀ k p n h → ⌈log₂ suc (length (proj₁ p) + length (proj₂ p)) ⌉ N.≤ k → Sorted (proj₁ p) → Sorted (proj₂ p) →
  ◯ (∃ λ splitters → bisplit/clocked k p n h ≡ ret splitters × NSplitters p n splitters)
bisplit/clocked/correct zero (a , b) n h h-clock sorted-a sorted-b u with ⌈log₂n⌉≡0⇒n≤1 {suc (length a + length b)} (N.n≤0⇒n≡0 h-clock)
bisplit/clocked/correct zero ([] , []) .zero z≤n h-clock [] [] u | s≤s z≤n = (([] , []) , ([] , [])) , refl , record
  { proof-a = refl
  ; proof-b = refl
  ; proof-align₁ = []
  ; proof-align₂ = []
  ; proof-n = refl
  }
bisplit/clocked/correct (suc k) ([] , b) n h h-clock sorted-a sorted-b u =
  let (b₁ , b₂ , h-≡ , length₁ , _ , h-++) = split/clocked/correct n (length b N.∸ n) b {!   !} u in
  (([] , []) , (b₁ , b₂)) , Eq.cong (λ e → bind (F pairs) e _) h-≡ , record
    { proof-a = refl
    ; proof-b = h-++
    ; proof-align₁ = []
    ; proof-align₂ = All.tabulate (const [])
    ; proof-n = length₁
    }
bisplit/clocked/correct (suc k) (a ∷ as , []) n h h-clock sorted-a sorted-b u =
  let (a₁ , a₂ , h-≡ , length₁ , _ , h-++) = split/clocked/correct n (length (a ∷ as) N.∸ n) (a ∷ as) {!   !} u in
  ((a₁ , a₂) , ([] , [])) , Eq.cong (λ e → bind (F pairs) e _) h-≡ , record
    { proof-a = h-++
    ; proof-b = refl
    ; proof-align₁ = All.tabulate (const [])
    ; proof-align₂ = []
    ; proof-n = Eq.trans (N.+-identityʳ _) length₁
    }
bisplit/clocked/correct (suc k) (a ∷ as , b ∷ bs) n h h-clock sorted-a sorted-b u
  with splitMid/correct (a ∷ as) (s≤s z≤n)
     | splitMid/correct (b ∷ bs) (s≤s z≤n)
... | (a₁ , aMid , a₂ , h-≡-a , length-a₁ , length-a₂ , h-++-a)
    | (b₁ , bMid , b₂ , h-≡-b , length-b₁ , length-b₂ , h-++-b)
      with h-cost aMid bMid | n N.≤? length a₁ + length b₁
... | ⇓ true  withCost c' [ h-bounded , h-≡-compare ] | yes p =
  let (((a₁' , a₂') , (b₁' , b₂')) , h-≡ , h-splitters) = bisplit/clocked/correct k (a ∷ as , b₁) n {!   !} {!   !} {!   !} {!   !} u in
  ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)) , {!   !} , (record
    { proof-a = NSplitters.proof-a h-splitters
    ; proof-b =
      let open ≡-Reasoning in
      begin
        b ∷ bs
      ≡⟨ h-++-b ⟩
        b₁ ++ [ bMid ] ++ b₂
      ≡⟨ Eq.cong (_++ [ bMid ] ++ b₂) (NSplitters.proof-b h-splitters) ⟩
        (b₁' ++ b₂') ++ [ bMid ] ++ b₂
      ≡⟨ ++-assoc b₁' b₂' ([ bMid ] ++ b₂) ⟩
        b₁' ++ (b₂' ++ [ bMid ] ++ b₂)
      ∎
    ; proof-align₁ = All.map (λ h-b₁ → {! h-b₁  !}) (NSplitters.proof-align₁ h-splitters)
    ; proof-align₂ = NSplitters.proof-align₂ h-splitters
    ; proof-n = NSplitters.proof-n h-splitters
    })
... | ⇓ false withCost c' [ h-bounded , h-≡-compare ] | yes p = {!   !}
... | ⇓ true  withCost c' [ h-bounded , h-≡-compare ] | no ¬p = {!   !}
... | ⇓ false withCost c' [ h-bounded , h-≡-compare ] | no ¬p =
  {!   !} , {!   !}

bisplit/clocked/cost : cmp (Π nat λ _ → Π pair λ (a , b) → Π nat λ n → Π (U (meta (n N.≤ length a + length b))) λ _ → cost)
bisplit/clocked/cost zero    (a      , b     ) n h = 𝟘
bisplit/clocked/cost (suc k) ([]     , b     ) n h = bind cost (split/clocked n b       ) λ bp → split/clocked/cost n b        ⊕ 𝟘
bisplit/clocked/cost (suc k) (a ∷ as , []    ) n h = bind cost (split/clocked n (a ∷ as)) λ ap → split/clocked/cost n (a ∷ as) ⊕ 𝟘
bisplit/clocked/cost (suc k) (a ∷ as , b ∷ bs) n h =
  bind cost (splitMid (a ∷ as) (s≤s z≤n)) λ (a₁ , aMid , a₂) → splitMid/cost (a ∷ as) (s≤s z≤n) ⊕
    bind cost (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) → splitMid/cost (b ∷ bs) (s≤s z≤n) ⊕
      bind cost (aMid ≤ᵇ bMid) λ condition → (1 , 1) ⊕ (
        if n N.≤ᵇ length a₁ + length b₁
          then
            if condition
              then
                (bind cost (bisplit/clocked k (a ∷ as , b₁) n {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a ∷ as , b₁) n {!   !} ⊕
                  𝟘)
              else
                (bind cost (bisplit/clocked k (a₁ , b ∷ bs) n {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a₁ , b ∷ bs) n {!   !} ⊕
                  𝟘)
          else
            if condition
              then
                (bind cost (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as))) {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as))) {!   !} ⊕
                  𝟘)
              else
                (bind cost (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs))) {!   !}) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs))) {!   !} ⊕
                  𝟘)
      )

bisplit/clocked/cost/closed : cmp (Π nat λ _ → Π pair λ (a , b) → Π nat λ n → Π (U (meta (n N.≤ length a + length b))) λ _ → cost)
bisplit/clocked/cost/closed k (a , b) n h = k , k

bisplit/clocked/cost≤bisplit/clocked/cost/closed : ∀ k p n h → ◯ (bisplit/clocked/cost k p n h ≤ₚ bisplit/clocked/cost/closed k p n h)
bisplit/clocked/cost≤bisplit/clocked/cost/closed = {!   !}

bisplit/clocked≤bisplit/clocked/cost : ∀ k p n h → IsBounded pairs (bisplit/clocked k p n h) (bisplit/clocked/cost k p n h)
bisplit/clocked≤bisplit/clocked/cost = {!   !}

bisplit/clocked≤bisplit/clocked/cost/closed : ∀ k p n h →
  IsBounded pairs (bisplit/clocked k p n h) (bisplit/clocked/cost/closed k p n h)
bisplit/clocked≤bisplit/clocked/cost/closed k p n h =
  bound/relax (bisplit/clocked/cost≤bisplit/clocked/cost/closed k p n h) (bisplit/clocked≤bisplit/clocked/cost k p n h)


merge : cmp (Π pair λ _ → F (list A))
merge = {!   !}

merge/correct : ∀ l₁ l₂ →
  ◯ (∃ λ l → merge (l₁ , l₂) ≡ ret l × (Sorted l₁ → Sorted l₂ → SortedOf (l₁ ++ l₂) l))
merge/correct = {!   !}

merge/cost : cmp (Π pair λ _ → cost)
merge/cost = {!   !}

merge/cost/closed : cmp (Π pair λ _ → cost)
merge/cost/closed = {!   !}

merge≤merge/cost : ∀ l₁ l₂ → IsBounded (list A) (merge (l₁ , l₂)) (merge/cost (l₁ , l₂))
merge≤merge/cost = {!   !}

merge≤merge/cost/closed : ∀ l₁ l₂ → IsBounded (list A) (merge (l₁ , l₂)) (merge/cost/closed (l₁ , l₂))
merge≤merge/cost/closed = {!   !}
