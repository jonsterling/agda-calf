open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.MergeSortPar (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.Parallel parCostMonoid
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_; ⌊_/2⌋; ⌈_/2⌉; _⊔_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Nat.Log2
open import Data.Nat.Square
open import Data.Nat.PredExp2


open import Examples.Sorting.Parallel.MergeSort.Split M public
open import Examples.Sorting.Parallel.MergeSortPar.Merge M public

sort/clocked : cmp (Π nat λ _ → Π (list A) λ _ → F (list A))
sort/clocked zero    l = ret l
sort/clocked (suc k) l =
  bind (F (list A)) (split l) λ (l₁ , l₂) →
    bind (F (list A)) (sort/clocked k l₁ ∥ sort/clocked k l₂) merge

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
        bind (F (list A)) (sort/clocked k l₁ ∥ sort/clocked k l₂) merge)
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
      bind (F (list A)) (sort/clocked k l₁ ∥ sort/clocked k l₂) merge
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e merge) (Eq.cong₂ _∥_ ≡₁ ≡₂) ⟩
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
sort/clocked/cost zero    l = 𝟘
sort/clocked/cost (suc k) l =
  bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
    bind cost (sort/clocked k l₁ ∥ sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
      merge/cost/closed (l₁' , l₂')

sort/clocked/cost/closed : cmp (Π nat λ _ → Π (list A) λ _ → cost)
sort/clocked/cost/closed k l = k * length l * ⌈log₂ suc ⌈ length l /2⌉ ⌉ , k * ⌈log₂ suc ⌈ length l /2⌉ ⌉ ²

sort/clocked/cost≤sort/clocked/cost/closed : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → ◯ (sort/clocked/cost k l ≤ₚ sort/clocked/cost/closed k l)
sort/clocked/cost≤sort/clocked/cost/closed zero    l h u = z≤n , z≤n
sort/clocked/cost≤sort/clocked/cost/closed (suc k) l h u =
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
  let open ≤ₚ-Reasoning in
  begin
    sort/clocked/cost (suc k) l
  ≡⟨⟩
    (bind cost (split l) λ (l₁ , l₂) → split/cost l ⊕
      bind cost (sort/clocked k l₁ ∥ sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂'))
  ≡⟨ Eq.cong (λ e → bind cost e _) (≡) ⟩
    (split/cost l ⊕
      bind cost (sort/clocked k l₁ ∥ sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂'))
  ≡⟨⟩
    (𝟘 ⊕
      bind cost (sort/clocked k l₁ ∥ sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂'))
  ≡⟨ ⊕-identityˡ _ ⟩
    (bind cost (sort/clocked k l₁ ∥ sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
      merge/cost/closed (l₁' , l₂'))
  ≡⟨
    Eq.cong (λ e → bind cost e λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕ merge/cost/closed (l₁' , l₂')) (
      Eq.cong₂ _∥_
        ≡₁
        ≡₂
    )
  ⟩
    (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕ merge/cost/closed (l₁' , l₂')
  ≤⟨
    ⊕-monoˡ-≤ (merge/cost/closed (l₁' , l₂')) (
      ⊗-mono-≤
        (sort/clocked/cost≤sort/clocked/cost/closed k l₁ h₁ u)
        (sort/clocked/cost≤sort/clocked/cost/closed k l₂ h₂ u)
    )
  ⟩
    (sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕ merge/cost/closed (l₁' , l₂')
  ≡⟨⟩
    (sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕
      (pred[2^ ⌈log₂ suc (length l₁') ⌉ ] * ⌈log₂ suc (length l₂') ⌉ , ⌈log₂ suc (length l₁') ⌉ * ⌈log₂ suc (length l₂') ⌉)
  ≡˘⟨
    Eq.cong ((sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕_) (
      Eq.cong₂ (λ n₁ n₂ →  pred[2^ ⌈log₂ suc n₁ ⌉ ] * ⌈log₂ suc n₂ ⌉ , ⌈log₂ suc n₁ ⌉ * ⌈log₂ suc n₂ ⌉)
        (↭-length ↭₁)
        (↭-length ↭₂)
    )
  ⟩
    (sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕
      (pred[2^ ⌈log₂ suc (length l₁) ⌉ ] * ⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₁) ⌉ * ⌈log₂ suc (length l₂) ⌉)
  ≡⟨⟩
    ((k * length l₁ * ⌈log₂ suc ⌈ length l₁ /2⌉ ⌉ , k * ⌈log₂ suc ⌈ length l₁ /2⌉ ⌉ ²) ⊗
      (k * length l₂ * ⌈log₂ suc ⌈ length l₂ /2⌉ ⌉ , k * ⌈log₂ suc ⌈ length l₂ /2⌉ ⌉ ²)) ⊕
      (pred[2^ ⌈log₂ suc (length l₁) ⌉ ] * ⌈log₂ suc (length l₂) ⌉ , ⌈log₂ suc (length l₁) ⌉ * ⌈log₂ suc (length l₂) ⌉)
  ≡⟨
    Eq.cong₂ (
      λ n₁ n₂ →
        ((k * n₁ * ⌈log₂ suc ⌈ n₁ /2⌉ ⌉ , k * ⌈log₂ suc ⌈ n₁ /2⌉ ⌉ ²) ⊗
          (k * n₂ * ⌈log₂ suc ⌈ n₂ /2⌉ ⌉ , k * ⌈log₂ suc ⌈ n₂ /2⌉ ⌉ ²)) ⊕
          (pred[2^ ⌈log₂ suc (n₁) ⌉ ] * ⌈log₂ suc (n₂) ⌉ , ⌈log₂ suc (n₁) ⌉ * ⌈log₂ suc (n₂) ⌉)
    )
      length₁
      length₂
  ⟩
    ((k * ⌊ length l /2⌋ * ⌈log₂ suc ⌈ ⌊ length l /2⌋ /2⌉ ⌉ , k * ⌈log₂ suc ⌈ ⌊ length l /2⌋ /2⌉ ⌉ ²) ⊗
      (k * ⌈ length l /2⌉ * ⌈log₂ suc ⌈ ⌈ length l /2⌉ /2⌉ ⌉ , k * ⌈log₂ suc ⌈ ⌈ length l /2⌉ /2⌉ ⌉ ²)) ⊕
      (pred[2^ ⌈log₂ suc ⌊ length l /2⌋ ⌉ ] * ⌈log₂ suc ⌈ length l /2⌉ ⌉ , ⌈log₂ suc ⌊ length l /2⌋ ⌉ * ⌈log₂ suc ⌈ length l /2⌉ ⌉)
  ≤⟨
    ⊕-mono-≤
      (
        let h-⌊n/2⌋ = log₂-mono (s≤s (N.⌈n/2⌉-mono (N.⌊n/2⌋≤n (length l))))
            h-⌈n/2⌉ = log₂-mono (s≤s (N.⌈n/2⌉-mono (N.⌈n/2⌉≤n (length l)))) in
        ⊗-mono-≤
          (N.*-monoʳ-≤ (k * ⌊ length l /2⌋) h-⌊n/2⌋ , N.*-monoʳ-≤ k (²-mono h-⌊n/2⌋))
          (N.*-monoʳ-≤ (k * ⌈ length l /2⌉) h-⌈n/2⌉ , N.*-monoʳ-≤ k (²-mono h-⌈n/2⌉))
      )
      (
        let h = log₂-mono (s≤s (N.⌊n/2⌋≤⌈n/2⌉ (length l))) in
        N.*-monoˡ-≤ ⌈log₂ suc ⌈ length l /2⌉ ⌉ (pred[2^]-mono h) ,
        N.*-monoˡ-≤ ⌈log₂ suc ⌈ length l /2⌉ ⌉ h
      )
  ⟩
    ((k * ⌊ length l /2⌋ * ⌈log₂ suc ⌈ length l /2⌉ ⌉ , k * ⌈log₂ suc ⌈ length l /2⌉ ⌉ ²) ⊗
      (k * ⌈ length l /2⌉ * ⌈log₂ suc ⌈ length l /2⌉ ⌉ , k * ⌈log₂ suc ⌈ length l /2⌉ ⌉ ²)) ⊕
      (pred[2^ ⌈log₂ suc ⌈ length l /2⌉ ⌉ ] * ⌈log₂ suc ⌈ length l /2⌉ ⌉ , ⌈log₂ suc ⌈ length l /2⌉ ⌉ ²)
  ≤⟨
    arithmetic/work (length l) ,
    (N.≤-reflexive (arithmetic/span (⌈log₂ suc ⌈ length l /2⌉ ⌉ ²)))
  ⟩
    suc k * length l * ⌈log₂ suc ⌈ length l /2⌉ ⌉ , suc k * ⌈log₂ suc ⌈ length l /2⌉ ⌉ ²
  ≡⟨⟩
    sort/clocked/cost/closed (suc k) l
  ∎
    where
      arithmetic/work : (n : ℕ) →
        (k * ⌊ n /2⌋ * ⌈log₂ suc ⌈ n /2⌉ ⌉ + k * ⌈ n /2⌉ * ⌈log₂ suc ⌈ n /2⌉ ⌉)
          + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉
        Nat.≤ suc k * n * ⌈log₂ suc ⌈ n /2⌉ ⌉
      arithmetic/work n =
        begin
          (k * ⌊ n /2⌋ * ⌈log₂ suc ⌈ n /2⌉ ⌉ + k * ⌈ n /2⌉ * ⌈log₂ suc ⌈ n /2⌉ ⌉)
            + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ≡⟨
          Eq.cong
            (_+ pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉)
            (Eq.cong₂ _+_
              (N.*-assoc k ⌊ n /2⌋ ⌈log₂ suc ⌈ n /2⌉ ⌉)
              (N.*-assoc k ⌈ n /2⌉ ⌈log₂ suc ⌈ n /2⌉ ⌉))
        ⟩
          (k * (⌊ n /2⌋ * ⌈log₂ suc ⌈ n /2⌉ ⌉) + k * (⌈ n /2⌉ * ⌈log₂ suc ⌈ n /2⌉ ⌉))
            + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ≡˘⟨
          Eq.cong (_+ pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉) (
            N.*-distribˡ-+ k (⌊ n /2⌋ * ⌈log₂ suc ⌈ n /2⌉ ⌉) (⌈ n /2⌉ * ⌈log₂ suc ⌈ n /2⌉ ⌉)
          )
        ⟩
          k * (⌊ n /2⌋ * ⌈log₂ suc ⌈ n /2⌉ ⌉ + ⌈ n /2⌉ * ⌈log₂ suc ⌈ n /2⌉ ⌉)
            + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ≡˘⟨
          Eq.cong
            (λ m → k * m + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉)
            (N.*-distribʳ-+ ⌈log₂ suc ⌈ n /2⌉ ⌉ ⌊ n /2⌋ ⌈ n /2⌉)
        ⟩
          k * ((⌊ n /2⌋ + ⌈ n /2⌉) * ⌈log₂ suc ⌈ n /2⌉ ⌉) + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ≡⟨
          Eq.cong
            (λ m → k * (m * ⌈log₂ suc ⌈ n /2⌉ ⌉) + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉)
            (N.⌊n/2⌋+⌈n/2⌉≡n n)
        ⟩
          k * (n * ⌈log₂ suc ⌈ n /2⌉ ⌉) + pred[2^ ⌈log₂ suc ⌈ n /2⌉ ⌉ ] * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ≤⟨ N.+-monoʳ-≤ (k * (n * ⌈log₂ suc ⌈ n /2⌉ ⌉)) (N.*-monoˡ-≤ ⌈log₂ suc ⌈ n /2⌉ ⌉ (pred[2^log₂] n)) ⟩
          k * (n * ⌈log₂ suc ⌈ n /2⌉ ⌉) + n * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ≡⟨ N.+-comm (k * (n * ⌈log₂ suc ⌈ n /2⌉ ⌉)) (n * ⌈log₂ suc ⌈ n /2⌉ ⌉) ⟩
          n * ⌈log₂ suc ⌈ n /2⌉ ⌉ + k * (n * ⌈log₂ suc ⌈ n /2⌉ ⌉)
        ≡⟨⟩
          suc k * (n * ⌈log₂ suc ⌈ n /2⌉ ⌉)
        ≡˘⟨ N.*-assoc (suc k) n ⌈log₂ suc ⌈ n /2⌉ ⌉ ⟩
          suc k * n * ⌈log₂ suc ⌈ n /2⌉ ⌉
        ∎
          where open ≤-Reasoning

      arithmetic/span : (n : ℕ) → ((k * n) ⊔ (k * n)) + n ≡ suc k * n
      arithmetic/span n =
        begin
          ((k * n) ⊔ (k * n)) + n
        ≡⟨ Eq.cong (_+ n) (N.⊔-idem (k * n)) ⟩
          k * n + n
        ≡⟨ N.+-comm (k * n) n ⟩
          n + k * n
        ≡⟨⟩
          suc k * n
        ∎
          where open ≡-Reasoning

sort/clocked≤sort/clocked/cost : ∀ k l → IsBounded (list A) (sort/clocked k l) (sort/clocked/cost k l)
sort/clocked≤sort/clocked/cost zero    l = bound/ret
sort/clocked≤sort/clocked/cost (suc k) l =
  bound/bind (split/cost l) _ (split≤split/cost l) λ (l₁ , l₂) →
    bound/bind (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) _ (bound/par (sort/clocked≤sort/clocked/cost k l₁) (sort/clocked≤sort/clocked/cost k l₂)) λ (l₁' , l₂') →
      merge≤merge/cost/closed l₁' l₂'

sort/clocked≤sort/clocked/cost/closed : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → IsBounded (list A) (sort/clocked k l) (sort/clocked/cost/closed k l)
sort/clocked≤sort/clocked/cost/closed k l h = bound/relax (sort/clocked/cost≤sort/clocked/cost/closed k l h) (sort/clocked≤sort/clocked/cost k l)

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

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n * ⌈log₂ n ⌉ ² , ⌈log₂ n ⌉ ^ 3)
sort/asymptotic = 2 ≤n⇒f[n]≤g[n]via λ l h →
  bound/relax
    (λ u → let open ≤-Reasoning in
      (
        begin
          ⌈log₂ length l ⌉ * length l * ⌈log₂ suc ⌈ length l /2⌉ ⌉
        ≤⟨ N.*-monoʳ-≤ (⌈log₂ length l ⌉ * length l) (lemma (length l) h) ⟩
          ⌈log₂ length l ⌉ * length l * ⌈log₂ length l ⌉
        ≡⟨ N.*-assoc ⌈log₂ length l ⌉ (length l) ⌈log₂ length l ⌉ ⟩
          ⌈log₂ length l ⌉ * (length l * ⌈log₂ length l ⌉)
        ≡⟨ N.*-comm ⌈log₂ length l ⌉ (length l * ⌈log₂ length l ⌉) ⟩
          length l * ⌈log₂ length l ⌉ * ⌈log₂ length l ⌉
        ≡⟨ N.*-assoc (length l) ⌈log₂ length l ⌉ ⌈log₂ length l ⌉ ⟩
          length l * ⌈log₂ length l ⌉ ²
        ∎
      ) , (
        begin
          ⌈log₂ length l ⌉ * ⌈log₂ suc ⌈ length l /2⌉ ⌉ ²
        ≤⟨ N.*-monoʳ-≤ ⌈log₂ length l ⌉ (²-mono (lemma (length l) h)) ⟩
          ⌈log₂ length l ⌉ * ⌈log₂ length l ⌉ ²
        ≡⟨⟩
          ⌈log₂ length l ⌉ * (⌈log₂ length l ⌉ * ⌈log₂ length l ⌉)
        ≡˘⟨ Eq.cong (λ n → ⌈log₂ length l ⌉ * (⌈log₂ length l ⌉ * n)) (N.*-identityʳ _) ⟩
          ⌈log₂ length l ⌉ * (⌈log₂ length l ⌉ * (⌈log₂ length l ⌉ * 1))
        ≡⟨⟩
          ⌈log₂ length l ⌉ ^ 3
        ∎
      )
    )
    (sort≤sort/cost/closed l)
  where
    lemma : ∀ n → 2 Nat.≤ n → ⌈log₂ suc ⌈ n /2⌉ ⌉ Nat.≤ ⌈log₂ n ⌉
    lemma (suc (suc n)) (s≤s (s≤s h)) = log₂-mono (s≤s (s≤s (N.⌈n/2⌉≤n n)))
