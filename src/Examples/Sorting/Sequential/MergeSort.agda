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
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as N
open import Data.Nat.Square
open import Data.Nat.Log2


open import Examples.Sorting.Sequential.MergeSort.Split M public
open import Examples.Sorting.Sequential.MergeSort.Merge M public

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
