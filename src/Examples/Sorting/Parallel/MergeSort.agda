{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.MergeSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Parallel.Core M

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Bounded costMonoid
open import Calf.Types.BigO costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉; _⊔_)
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Nat.Log2


open import Examples.Sorting.Parallel.MergeSort.Split M public
open import Examples.Sorting.Parallel.MergeSort.Merge M public

sort/clocked : cmp (Π nat λ _ → Π (list A) λ _ → F (list A))
sort/clocked zero    l = ret l
sort/clocked (suc k) l =
  bind (F (list A)) (split l) λ (l₁ , l₂) →
    bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge

sort/clocked/correct : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → SortResult (sort/clocked k) l
sort/clocked/correct zero    l h u = l , refl , refl , short-sorted (⌈log₂n⌉≡0⇒n≤1 (N.n≤0⇒n≡0 h))
sort/clocked/correct (suc k) l h u =
  let (l₁ , l₂ , ≡ , length₁ , length₂ , h-++) = split/correct l u in
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
        bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge)
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e _) ≡ ⟩
      bind (F (list A)) (sort/clocked k l₁ & sort/clocked k l₂) merge
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e merge) (Eq.cong₂ _&_ ≡₁ ≡₂) ⟩
      merge (l₁' , l₂')
    ≡⟨ ≡' ⟩
      ret l'
    ∎
  ) , (
    let open PermutationReasoning in
    begin
      l
    ≡⟨ h-++ ⟩
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
    bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
      merge/cost/closed (l₁' , l₂')

sort/clocked/cost/closed : cmp (Π nat λ _ → Π (list A) λ _ → cost)
sort/clocked/cost/closed k l = k * length l , 2 * length l + k

sort/clocked/cost≤sort/clocked/cost/closed : ∀ k l → ⌈log₂ length l ⌉ Nat.≤ k → ◯ (sort/clocked/cost k l ≤ₚ sort/clocked/cost/closed k l)
sort/clocked/cost≤sort/clocked/cost/closed zero    l h u = z≤n , z≤n
sort/clocked/cost≤sort/clocked/cost/closed (suc k) l h u =
  let (l₁ , l₂ , ≡ , length₁ , length₂ , _) = split/correct l u in
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
      bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂'))
  ≡⟨ Eq.cong (λ e → bind cost e _) (≡) ⟩
    (split/cost l ⊕
      bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂'))
  ≡⟨⟩
    (𝟘 ⊕
      bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
        merge/cost/closed (l₁' , l₂'))
  ≡⟨ ⊕-identityˡ _ ⟩
    (bind cost (sort/clocked k l₁ & sort/clocked k l₂) λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕
      merge/cost/closed (l₁' , l₂'))
  ≡⟨ Eq.cong (λ e → bind cost e λ (l₁' , l₂') → (sort/clocked/cost k l₁ ⊗ sort/clocked/cost k l₂) ⊕ merge/cost/closed (l₁' , l₂')) (Eq.cong₂ _&_ ≡₁ ≡₂) ⟩
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
      (length l₁' + length l₂' , length l₁' + length l₂')
  ≡˘⟨
    Eq.cong ((sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕_) (
      Eq.cong₂ (λ n₁ n₂ → (n₁ + n₂ , n₁ + n₂))
        (↭-length ↭₁)
        (↭-length ↭₂)
    )
  ⟩
    (sort/clocked/cost/closed k l₁ ⊗ sort/clocked/cost/closed k l₂) ⊕
      (length l₁ + length l₂ , length l₁ + length l₂)
  ≡⟨⟩
    ((k * length l₁ , 2 * length l₁ + k) ⊗ (k * length l₂ , 2 * length l₂ + k)) ⊕
      (length l₁ + length l₂ , length l₁ + length l₂)
  ≡⟨
    Eq.cong₂
      (λ n₁ n₂ → ((k * n₁ , 2 * n₁ + k) ⊗ (k * n₂ , 2 * n₂ + k)) ⊕ (n₁ + n₂ , n₁ + n₂))
      length₁
      length₂
  ⟩
    ((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕
      (⌊ length l /2⌋ + ⌈ length l /2⌉ , ⌊ length l /2⌋ + ⌈ length l /2⌉)
  ≡⟨
    Eq.cong (((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕_) (
      Eq.cong₂ _,_ (N.⌊n/2⌋+⌈n/2⌉≡n (length l)) (N.⌊n/2⌋+⌈n/2⌉≡n (length l))
    )
  ⟩
    ((k * ⌊ length l /2⌋ , 2 * ⌊ length l /2⌋ + k) ⊗ (k * ⌈ length l /2⌉ , 2 * ⌈ length l /2⌉ + k)) ⊕
      (length l , length l)
  ≤⟨ arithmetic/work (length l) , arithmetic/span (length l) ⟩
    suc k * length l , 2 * length l + suc k
  ≡⟨⟩
    sort/clocked/cost/closed (suc k) l
  ∎
    where
      arithmetic/work : ∀ n → k * ⌊ n /2⌋ + k * ⌈ n /2⌉ + n Nat.≤ suc k * n
      arithmetic/work n =
        begin
          k * ⌊ n /2⌋ + k * ⌈ n /2⌉ + n
        ≡⟨ N.+-comm _ n ⟩
          n + (k * ⌊ n /2⌋ + k * ⌈ n /2⌉)
        ≡˘⟨ Eq.cong (n +_) (N.*-distribˡ-+ k _ _) ⟩
          n + k * (⌊ n /2⌋ + ⌈ n /2⌉)
        ≡⟨ Eq.cong (λ m → n + k * m) (N.⌊n/2⌋+⌈n/2⌉≡n n) ⟩
          n + k * n
        ≡⟨⟩
          suc k * n
        ∎
          where open ≤-Reasoning

      lemma/2n≡n+n : ∀ n → 2 * n ≡ n + n
      lemma/2n≡n+n n = Eq.cong (λ m → n + m) (N.+-identityʳ n)

      arithmetic/span : ∀ n → (2 * ⌊ n /2⌋ + k) ⊔ (2 * ⌈ n /2⌉ + k) + n Nat.≤ 2 * n + suc k
      arithmetic/span n =
        begin
          (2 * ⌊ n /2⌋ + k) ⊔ (2 * ⌈ n /2⌉ + k) + n
        ≤⟨ N.+-monoˡ-≤ n (N.⊔-monoˡ-≤ (2 * ⌈ n /2⌉ + k) (N.+-monoˡ-≤ k (N.*-monoʳ-≤ 2 (N.⌊n/2⌋≤⌈n/2⌉ n)))) ⟩
          (2 * ⌈ n /2⌉ + k) ⊔ (2 * ⌈ n /2⌉ + k) + n
        ≡⟨ Eq.cong (_+ n) (N.⊔-idem _) ⟩
          2 * ⌈ n /2⌉ + k + n
        ≡⟨ N.+-assoc (2 * ⌈ n /2⌉) k n ⟩
          2 * ⌈ n /2⌉ + (k + n)
        ≡⟨ Eq.cong (_+ (k + n)) (lemma/2n≡n+n ⌈ n /2⌉) ⟩
          (⌈ n /2⌉ + ⌈ n /2⌉) + (k + n)
        ≡⟨⟩
          (⌊ suc n /2⌋ + ⌈ n /2⌉) + (k + n)
        ≤⟨ N.+-monoˡ-≤ (k + n) (N.+-monoʳ-≤ ⌊ suc n /2⌋ (N.⌈n/2⌉-mono (N.n≤1+n n))) ⟩
          (⌊ suc n /2⌋ + ⌈ suc n /2⌉) + (k + n)
        ≡⟨ Eq.cong (_+ (k + n)) (N.⌊n/2⌋+⌈n/2⌉≡n (suc n)) ⟩
          suc n + (k + n)
        ≡⟨⟩
          suc (n + (k + n))
        ≡⟨ Eq.cong (λ m → suc (n + m)) (N.+-comm k n) ⟩
          suc (n + (n + k))
        ≡˘⟨ Eq.cong suc (N.+-assoc n n k) ⟩
          suc ((n + n) + k)
        ≡˘⟨ N.+-suc (n + n) k ⟩
          (n + n) + suc k
        ≡˘⟨ Eq.cong (_+ suc k) (lemma/2n≡n+n n) ⟩
          2 * n + suc k
        ∎
          where open ≤-Reasoning

sort/clocked≤sort/clocked/cost : ∀ k l → IsBounded (list A) (sort/clocked k l) (sort/clocked/cost k l)
sort/clocked≤sort/clocked/cost zero l = bound/ret
sort/clocked≤sort/clocked/cost (suc k) l =
  bound/bind _ _ (split≤split/cost l) λ (l₁ , l₂) →
    bound/bind _ _ (bound/par (sort/clocked≤sort/clocked/cost k l₁) (sort/clocked≤sort/clocked/cost k l₂)) λ (l₁' , l₂') →
      merge≤merge/cost/closed (l₁' , l₂')

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

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n * ⌈log₂ n ⌉ , n)
sort/asymptotic = 0 ≤n⇒f[n]≤ 3 g[n]via λ l _ →
  bound/relax
    (λ u → let open ≤-Reasoning in
      (
        begin
          ⌈log₂ length l ⌉ * length l
        ≡⟨ N.*-comm ⌈log₂ length l ⌉ (length l) ⟩
          length l * ⌈log₂ length l ⌉
        ≤⟨ N.m≤m+n (length l * ⌈log₂ length l ⌉) _ ⟩
          3 * (length l * ⌈log₂ length l ⌉)
        ∎
      ) , (
        begin
          2 * length l + ⌈log₂ length l ⌉
        ≤⟨ N.+-monoʳ-≤ (2 * length l) (⌈log₂n⌉≤n (length l)) ⟩
          2 * length l + length l
        ≡⟨ N.+-comm (2 * length l) (length l) ⟩
          3 * length l
        ∎
      )
    )
    (sort≤sort/cost/closed l)
