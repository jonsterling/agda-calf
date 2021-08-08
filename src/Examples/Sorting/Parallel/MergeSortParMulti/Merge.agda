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
open import Data.Nat as N using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_; _*_; ⌊_/2⌋; ⌈_/2⌉; pred; _⊔_)
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

bisplit/clocked : cmp (Π nat λ _ → Π pair λ _ → Π nat λ _ → F pairs)
bisplit/clocked zero    (a      , b     ) n = ret ((a , []) , (b , []))
bisplit/clocked (suc k) ([]     , b     ) n = bind (F pairs) (split/clocked n b       ) λ bp → ret (([] , []) , bp)
bisplit/clocked (suc k) (a ∷ as , []    ) n = bind (F pairs) (split/clocked n (a ∷ as)) λ ap → ret (ap , ([] , []))
bisplit/clocked (suc k) (a ∷ as , b ∷ bs) n =
  bind (F pairs) (splitMid (a ∷ as) (s≤s z≤n)) λ (a₁ , aMid , a₂) →
    bind (F pairs) (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) →
      bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
        if n N.≤ᵇ length a₁ + length b₁
          then
            if condition
              then
                (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
              else
                (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
          else
            if condition
              then
                (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
              else
                (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
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
    proof-align₁ : All (_≤* b₂) a₁
    proof-align₂ : All (_≤* a₂) b₁
    proof-n : length a₁ + length b₁ ≡ n

private
  lemma/≤ᵇ : ∀ {m n} → m N.≤ n → (m N.≤ᵇ n) ≡ true
  lemma/≤ᵇ {m} {n} m≤n with m N.≤ᵇ n | N.≤ᵇ-reflects-≤ m n
  ... | .true  | ofʸ _ = refl
  ... | .false | ofⁿ ¬m≤n = contradiction m≤n ¬m≤n

bisplit/clocked/correct : ∀ k p n →
  n N.≤ length (proj₁ p) + length (proj₂ p) →
  ⌈log₂ suc (length (proj₁ p)) ⌉ + ⌈log₂ suc (length (proj₂ p)) ⌉ N.≤ k →
  Sorted (proj₁ p) →
  Sorted (proj₂ p) →
  ◯ (∃ λ splitters → bisplit/clocked k p n ≡ ret splitters × NSplitters p n splitters)
bisplit/clocked/correct zero (a , b) n h h-clock sorted-a sorted-b u
  with ⌈log₂n⌉≡0⇒n≤1 {suc (length a)} (N.n≤0⇒n≡0 (N.m+n≤o⇒m≤o ⌈log₂ suc (length a) ⌉ h-clock))
     | ⌈log₂n⌉≡0⇒n≤1 {suc (length b)} (N.n≤0⇒n≡0 (N.m+n≤o⇒n≤o ⌈log₂ suc (length a) ⌉ h-clock))
bisplit/clocked/correct zero ([] , []) .zero z≤n h-clock [] [] u | s≤s z≤n | s≤s z≤n = (([] , []) , ([] , [])) , refl , record
  { proof-a = refl
  ; proof-b = refl
  ; proof-align₁ = []
  ; proof-align₂ = []
  ; proof-n = refl
  }
bisplit/clocked/correct (suc k) ([] , b) n h h-clock sorted-a sorted-b u =
  let (b₁ , b₂ , h-≡ , length₁ , _ , h-++) = split/clocked/correct n (length b N.∸ n) b (
                                              let open ≡-Reasoning in
                                              begin
                                                n + (length b N.∸ n)
                                              ≡⟨ N.+-comm n (length b N.∸ n) ⟩
                                                (length b N.∸ n) + n
                                              ≡⟨ N.m∸n+n≡m h ⟩
                                                length b
                                              ∎
                                             ) u in
  (([] , []) , (b₁ , b₂)) , Eq.cong (λ e → bind (F pairs) e _) h-≡ , record
    { proof-a = refl
    ; proof-b = h-++
    ; proof-align₁ = []
    ; proof-align₂ = All.tabulate (const [])
    ; proof-n = length₁
    }
bisplit/clocked/correct (suc k) (a ∷ as , []) n h h-clock sorted-a sorted-b u =
  let (a₁ , a₂ , h-≡ , length₁ , _ , h-++) = split/clocked/correct n (length (a ∷ as) N.∸ n) (a ∷ as) (
                                              let open ≡-Reasoning in
                                              begin
                                                n + (length (a ∷ as) N.∸ n)
                                              ≡⟨ N.+-comm n (length (a ∷ as) N.∸ n) ⟩
                                                (length (a ∷ as) N.∸ n) + n
                                              ≡⟨ N.m∸n+n≡m (N.≤-trans h (N.≤-reflexive (N.+-identityʳ _))) ⟩
                                                length (a ∷ as)
                                              ∎
                                             ) u in
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
bisplit/clocked/correct (suc k) (a ∷ as , b ∷ bs) n h h-clock sorted-a sorted-b u
    | (a₁ , aMid , a₂ , h-≡-a , length-a₁ , length-a₂ , h-++-a)
    | (b₁ , bMid , b₂ , h-≡-b , length-b₁ , length-b₂ , h-++-b)
    | ⇓ true  withCost c' [ h-bounded , h-≡-condition ] | yes n≤a₁+b₁ =
  let sorted-b' = Eq.subst Sorted h-++-b sorted-b in
  let (((a₁' , a₂') , (b₁' , b₂')) , h-≡ , h-splitters) = bisplit/clocked/correct k (a ∷ as , b₁) n (
                                                            let open ≤-Reasoning in
                                                            begin
                                                              n
                                                            ≤⟨ n≤a₁+b₁ ⟩
                                                              length a₁ + length b₁
                                                            ≤⟨ N.+-monoˡ-≤ (length b₁) (N.m≤m+n (length a₁) (length (aMid ∷ a₂))) ⟩
                                                              (length a₁ + length (aMid ∷ a₂)) + length b₁
                                                            ≡˘⟨ Eq.cong (λ l → l + length b₁) (length-++ a₁) ⟩
                                                              length (a₁ ++ aMid ∷ a₂) + length b₁
                                                            ≡˘⟨ Eq.cong (λ l → length l + length b₁) h-++-a ⟩
                                                              length (a ∷ as) + length b₁
                                                            ∎
                                                          ) (
                                                            let open ≤-Reasoning in
                                                            begin
                                                              ⌈log₂ suc (length (a ∷ as)) ⌉ + ⌈log₂ suc (length b₁) ⌉
                                                            ≤⟨ N.+-monoʳ-≤ ⌈log₂ suc (length (a ∷ as)) ⌉ (log₂-mono (s≤s length-b₁)) ⟩
                                                              ⌈log₂ suc (length (a ∷ as)) ⌉ + ⌈log₂ ⌈ suc (length (b ∷ bs)) /2⌉ ⌉
                                                            ≤⟨
                                                              N.+-cancelˡ-≤ 1 $
                                                                begin
                                                                  suc (⌈log₂ suc (length (a ∷ as)) ⌉ + ⌈log₂ ⌈ suc (length (b ∷ bs)) /2⌉ ⌉)
                                                                ≡˘⟨ N.+-suc ⌈log₂ suc (length (a ∷ as)) ⌉ ⌈log₂ ⌈ suc (length (b ∷ bs)) /2⌉ ⌉ ⟩
                                                                  ⌈log₂ suc (length (a ∷ as)) ⌉ + suc ⌈log₂ ⌈ suc (length (b ∷ bs)) /2⌉ ⌉
                                                                ≡⟨⟩
                                                                  ⌈log₂ suc (length (a ∷ as)) ⌉ + ⌈log₂ suc (length (b ∷ bs)) ⌉
                                                                ≤⟨ h-clock ⟩
                                                                  suc k
                                                                ∎
                                                            ⟩
                                                              k
                                                            ∎
                                                          ) sorted-a (++⁻ˡ b₁ sorted-b') u in
  ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)) , (
    let open ≡-Reasoning in
    begin
      bisplit/clocked (suc k) (a ∷ as , b ∷ bs) n
    ≡⟨⟩
      (bind (F pairs) (splitMid (a ∷ as) (s≤s z≤n)) λ (a₁ , aMid , a₂) →
        bind (F pairs) (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) →
          bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
            if n N.≤ᵇ length a₁ + length b₁
              then
                if condition
                  then
                    (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
                  else
                    (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
              else
                if condition
                  then
                    (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
                  else
                    (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂'))))
    ≡⟨
      Eq.cong
        (λ e →
          bind (F pairs) e λ (a₁ , aMid , a₂) →
            bind (F pairs) (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) →
              bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
                if n N.≤ᵇ length a₁ + length b₁
                  then
                    if condition
                      then
                        (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                          ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
                      else
                        (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                          ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
                  else
                    if condition
                      then
                        (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                          ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
                      else
                        (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                          ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂')))
        )
        (h-≡-a u)
    ⟩
      (bind (F pairs) (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) →
        bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
          if n N.≤ᵇ length a₁ + length b₁
            then
              if condition
                then
                  (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                    ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
                else
                  (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                    ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
            else
              if condition
                then
                  (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                    ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
                else
                  (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                    ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂'))))
    ≡⟨
      Eq.cong
        (λ e →
          bind (F pairs) e λ (b₁ , bMid , b₂) →
            bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
              if n N.≤ᵇ length a₁ + length b₁
                then
                  if condition
                    then
                      (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                        ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
                    else
                      (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                        ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
                else
                  if condition
                    then
                      (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                        ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
                    else
                      (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                        ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂')))
        )
        (h-≡-b u)
    ⟩
      (bind (F pairs) (aMid ≤ᵇ bMid) λ condition →
        if n N.≤ᵇ length a₁ + length b₁
          then
            if condition
              then
                (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
              else
                (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
          else
            if condition
              then
                (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
              else
                (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                  ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂'))))
    ≡⟨
      Eq.cong
        (λ e →
          bind (F pairs) e λ condition →
            if n N.≤ᵇ length a₁ + length b₁
              then
                if condition
                  then
                    (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
                  else
                    (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
              else
                if condition
                  then
                    (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
                  else
                    (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                      ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂')))
        )
        (Eq.trans (eq/ref h-≡-condition) (step/ext (F bool) (ret true) c' u))
    ⟩
      (if n N.≤ᵇ length a₁ + length b₁
        then
          if true
            then
              (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
            else
              (bind (F pairs) (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                ret ((a₁' , a₂' ++ [ aMid ] ++ a₂) , (b₁' , b₂')))
        else
          if true
            then
              (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
            else
              (bind (F pairs) (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                ret ((a₁' , a₂') , (b₁ ++ [ bMid ] ++ b₁' , b₂'))))
    ≡⟨⟩
      (if n N.≤ᵇ length a₁ + length b₁
        then
          (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
            ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
        else
          (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
            ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂'))))
    ≡⟨
      Eq.cong
        (λ e →
          if e
            then
              (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
                ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
            else
              (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
                ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂')))
        )
        (lemma/≤ᵇ n≤a₁+b₁)
    ⟩
      (if true
        then
          (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
            ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
        else
          (bind (F pairs) (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) →
            ret ((a₁ ++ [ aMid ] ++ a₁' , a₂') , (b₁' , b₂'))))
    ≡⟨⟩
      (bind (F pairs) (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) →
        ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂)))
    ≡⟨ Eq.cong (λ e → bind (F pairs) e _) h-≡ ⟩
      ret ((a₁' , a₂') , (b₁' , b₂' ++ [ bMid ] ++ b₂))
    ∎
  ) , record
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
    ; proof-align₁ =
      All.map
        (λ {aᵢ} h-b₂' →
          let aᵢ≤bMid : aᵢ ≤ bMid
              aᵢ≤bMid = {!   !}
          in
          All.++⁺ h-b₂' (aᵢ≤bMid ∷ ≤-≤* aᵢ≤bMid (uncons₁ (++⁻ʳ b₁ sorted-b'))))
        (NSplitters.proof-align₁ h-splitters)
    ; proof-align₂ = NSplitters.proof-align₂ h-splitters
    ; proof-n = NSplitters.proof-n h-splitters
    }
bisplit/clocked/correct (suc k) (a ∷ as , b ∷ bs) n h h-clock sorted-a sorted-b u
    | (a₁ , aMid , a₂ , h-≡-a , length-a₁ , length-a₂ , h-++-a)
    | (b₁ , bMid , b₂ , h-≡-b , length-b₁ , length-b₂ , h-++-b)
    | ⇓ true  withCost c' [ h-bounded , h-≡-condition ] | no ¬n≤a₁+b₁ = {!   !}
bisplit/clocked/correct (suc k) (a ∷ as , b ∷ bs) n h h-clock sorted-a sorted-b u
    | (a₁ , aMid , a₂ , h-≡-a , length-a₁ , length-a₂ , h-++-a)
    | (b₁ , bMid , b₂ , h-≡-b , length-b₁ , length-b₂ , h-++-b)
    | ⇓ false withCost c' [ h-bounded , h-≡-condition ] | todo = {!   !}

bisplit/clocked/cost : cmp (Π nat λ _ → Π pair λ _ → Π nat λ _ → cost)
bisplit/clocked/cost zero    (a      , b     ) n = 𝟘
bisplit/clocked/cost (suc k) ([]     , b     ) n = bind cost (split/clocked n b       ) λ bp → split/clocked/cost n b        ⊕ 𝟘
bisplit/clocked/cost (suc k) (a ∷ as , []    ) n = bind cost (split/clocked n (a ∷ as)) λ ap → split/clocked/cost n (a ∷ as) ⊕ 𝟘
bisplit/clocked/cost (suc k) (a ∷ as , b ∷ bs) n =
  bind cost (splitMid (a ∷ as) (s≤s z≤n)) λ (a₁ , aMid , a₂) → splitMid/cost (a ∷ as) (s≤s z≤n) ⊕
    bind cost (splitMid (b ∷ bs) (s≤s z≤n)) λ (b₁ , bMid , b₂) → splitMid/cost (b ∷ bs) (s≤s z≤n) ⊕
      bind cost (aMid ≤ᵇ bMid) λ condition → (1 , 1) ⊕ (
        if n N.≤ᵇ length a₁ + length b₁
          then
            if condition
              then
                (bind cost (bisplit/clocked k (a ∷ as , b₁) n) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a ∷ as , b₁) n ⊕
                  𝟘)
              else
                (bind cost (bisplit/clocked k (a₁ , b ∷ bs) n) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a₁ , b ∷ bs) n ⊕
                  𝟘)
          else
            if condition
              then
                (bind cost (bisplit/clocked k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as)))) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a₂ , b ∷ bs) (n N.∸ suc (length (a ∷ as))) ⊕
                  𝟘)
              else
                (bind cost (bisplit/clocked k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs)))) λ ((a₁' , a₂') , (b₁' , b₂')) → bisplit/clocked/cost k (a ∷ as , b₂) (n N.∸ suc (length (b ∷ bs))) ⊕
                  𝟘)
      )

bisplit/clocked/cost/closed : cmp (Π nat λ _ → Π pair λ _ → Π nat λ _ → cost)
bisplit/clocked/cost/closed k (a , b) n = k , k

bisplit/clocked/cost≤bisplit/clocked/cost/closed : ∀ k p n → ◯ (bisplit/clocked/cost k p n ≤ₚ bisplit/clocked/cost/closed k p n)
bisplit/clocked/cost≤bisplit/clocked/cost/closed = {!   !}

bisplit/clocked≤bisplit/clocked/cost : ∀ k p n → IsBounded pairs (bisplit/clocked k p n) (bisplit/clocked/cost k p n)
bisplit/clocked≤bisplit/clocked/cost = {!   !}

bisplit/clocked≤bisplit/clocked/cost/closed : ∀ k p n →
  IsBounded pairs (bisplit/clocked k p n) (bisplit/clocked/cost/closed k p n)
bisplit/clocked≤bisplit/clocked/cost/closed k p n =
  bound/relax (bisplit/clocked/cost≤bisplit/clocked/cost/closed k p n) (bisplit/clocked≤bisplit/clocked/cost k p n)


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
