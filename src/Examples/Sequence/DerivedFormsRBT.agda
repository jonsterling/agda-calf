{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.DerivedFormsRBT where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Parallel parCostMonoid

open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.Product
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid
open import Data.List as List hiding (sum; map)
import Data.List.Properties as List
open import Data.Nat as Nat using (_+_; _*_)
import Data.Nat.Properties as Nat
open import Data.Nat.Logarithm

open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

open import Examples.Sequence.RedBlackTree


module MapReduce {A B : tp⁺} where
  mapreduce : cmp $
    Π color λ y → Π nat λ n → Π (list A) λ l → Π (irbt A y n l) λ _ →
    Π (U (Π A λ _ → F B)) λ _ →
    Π (U (Π B λ _ → Π B λ _ → F B)) λ _ →
    Π B λ _ →
    F B
  mapreduce .black .zero .[] leaf f g z = ret z
  mapreduce .red n l (red t₁ a t₂) f g z =
    bind (F B)
      ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ s →
        bind (F B) (f a) (λ b →
          bind (F B) (g b (proj₂ s)) (λ s₃ →
            bind (F B) (g (proj₁ s) s₃) ret))
  mapreduce .black n@(suc n') l (black t₁ a t₂) f g z =
    bind (F B)
      ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ s →
        bind (F B) (f a) (λ b →
          bind (F B) (g b (proj₂ s)) (λ s₃ →
            bind (F B) (g (proj₁ s) s₃) ret))

  mapreduce/cost/work : val color → val nat → val nat
  mapreduce/cost/work red n = 12 * (4 ^ (n ∸ 1)) ∸ 3
  mapreduce/cost/work black n = 6 * (4 ^ (n ∸ 1)) ∸ 3

  mapreduce/cost/work' : val nat → val nat
  mapreduce/cost/work' n = 12 * (4 ^ (n ∸ 1)) ∸ 3

  mapreduce/cost/work≤mapreduce/cost/work' : (y : val color) → (n : val nat) → mapreduce/cost/work y n Nat.≤ mapreduce/cost/work' n
  mapreduce/cost/work≤mapreduce/cost/work' red n = Nat.≤-refl
  mapreduce/cost/work≤mapreduce/cost/work' black n =
    Nat.∸-monoˡ-≤ {n = 12 * (4 ^ (n ∸ 1))} 3
      (Nat.*-monoˡ-≤ (4 ^ (n ∸ 1)) {y = 12} (Nat.s≤s (Nat.s≤s (Nat.s≤s (Nat.s≤s (Nat.s≤s (Nat.s≤s Nat.z≤n)))))))

  mapreduce/cost/span : val color → val nat → val nat
  mapreduce/cost/span red n = 6 * n
  mapreduce/cost/span black n = 6 * n ∸ 3

  mapreduce/cost/span' : val nat → val nat
  mapreduce/cost/span' n = 6 * n

  mapreduce/cost/span≤mapreduce/cost/span' : (y : val color) → (n : val nat) → mapreduce/cost/span y n Nat.≤ mapreduce/cost/span' n
  mapreduce/cost/span≤mapreduce/cost/span' red n = Nat.≤-refl
  mapreduce/cost/span≤mapreduce/cost/span' black n = Nat.m∸n≤m (6 * n) 3

  mapreduce/is-bounded :
    (f : cmp (Π A λ _ → F B)) →
    ({x : val A} → IsBounded B (f x) (1 , 1)) →
    (g : cmp (Π B λ _ → Π B λ _ → F B)) →
    ({x y : val B} → IsBounded B (g x y) (1 , 1)) →
    (z : val B) →
    (y : val color) → (n : val nat) → (l : val (list A)) → (t : val (irbt A y n l)) →
    IsBounded B (mapreduce y n l t f g z) (mapreduce/cost/work y n , mapreduce/cost/span y n)
  mapreduce/is-bounded f f-bound g g-bound z .black .zero .[] leaf =
    step⋆-mono-≤⁻ {c' = 3 , 0} (Nat.z≤n , Nat.z≤n)
  mapreduce/is-bounded f f-bound g g-bound z .red n l (red t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (
          bind (F B)
            ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ _ →
              bind (F B) (f a) (λ _ →
                bind (F B) (g _ _) (λ _ →
                  bind (F B) (g _ _) ret)))
          (λ _ → ret triv)
      ≡⟨⟩
        (
          bind cost
            ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ s₃ →
                  bind cost (g s₁ s₃) λ _ →
                    ret triv
        )
      ≤⟨ {! ≤⁻-mono (λ e →
          bind cost
            ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ s₃ →
                  bind cost e λ _ →
                    ret triv) ?  !} ⟩
       (
          bind cost
            ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ s₃ →
                  step⋆ (1 , 1)
        )
      ≤⟨ {!   !} ⟩
        {!   !}
      ∎
  mapreduce/is-bounded f f-bound g g-bound z .black n@(suc n') l (black t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        {!   !}
      ≤⟨ {!   !} ⟩
        {!   !}
      ∎

  mapreduce/is-bounded' :
    (f : cmp (Π A λ _ → F B)) →
    ({x : val A} → IsBounded B (f x) (1 , 1)) →
    (g : cmp (Π B λ _ → Π B λ _ → F B)) →
    ({x y : val B} → IsBounded B (g x y) (1 , 1)) →
    (z : val B) →
    (y : val color) → (n : val nat) → (l : val (list A)) → (t : val (irbt A y n l)) →
    IsBounded B (mapreduce y n l t f g z) (mapreduce/cost/work' n , mapreduce/cost/span' n)
  mapreduce/is-bounded' f f-bound g g-bound z y n l t =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (mapreduce y n l t f g z) (λ _ → ret triv)
      ≤⟨ mapreduce/is-bounded f f-bound g g-bound z y n l t ⟩
        step⋆ (mapreduce/cost/work y n , mapreduce/cost/span y n)
      ≤⟨ step⋆-mono-≤⁻ (mapreduce/cost/work≤mapreduce/cost/work' y n , mapreduce/cost/span≤mapreduce/cost/span' y n) ⟩
        step⋆ (mapreduce/cost/work' n , mapreduce/cost/span' n)
      ∎


module Sum where
  sum/seq : cmp $
    Π color λ y → Π nat λ n → Π (list nat) λ l → Π (irbt nat y n l) λ _ → F nat
  sum/seq .black .zero .[] leaf = ret 0
  sum/seq .red n l (red t₁ a t₂) =
    step (F nat) (1 , 1) $
      bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
      (λ (s₁ , s₂) → ret (s₁ + a + s₂))
  sum/seq .black n l (black t₁ a t₂) =
    step (F nat) (1 , 1) $
      bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
      (λ (s₁ , s₂) → ret (s₁ + a + s₂))

  span/sum : val color → val nat → val nat
  span/sum red n = 1 + 2 * n
  span/sum black n = 2 * n

  span/bounded : ∀ y n → (span/sum y n) Nat.≤ (1 + 2 * n)
  span/bounded red n = Nat.≤-refl
  span/bounded black n = Nat.n≤1+n (2 * n)

  list/preserves/length : ∀ (l₁ : List ℕ) a (l₂ : List ℕ) → 1 + (length l₁ + length l₂) ≡ length (l₁ ++ a ∷ l₂)
  list/preserves/length l₁ a l₂ =
    let open ≡-Reasoning in
    begin
      1 + (length l₁ + length l₂)
    ≡˘⟨ Nat.+-assoc 1 (length l₁) (length l₂) ⟩
      1 + length l₁ + length l₂
    ≡⟨ Eq.cong₂ _+_ (Nat.+-comm 1 (length l₁)) refl ⟩
      length l₁ + 1 + length l₂
    ≡⟨ Nat.+-assoc (length l₁) 1 (length l₂) ⟩
      length l₁ + (1 + length l₂)
    ≡⟨⟩
      length l₁ + length (a ∷ l₂)
    ≡˘⟨ List.length-++ l₁ ⟩
      length (l₁ ++ a ∷ l₂)
    ∎

  sum/bounded' : ∀ y n l t → IsBounded nat (sum/seq y n l t) (length l , span/sum y n)
  sum/bounded' .black .zero .[] leaf = ≤⁻-refl
  sum/bounded' .red n l (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        step cost (1 , 1) (
          bind cost (
            bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
              (λ (s₁ , s₂) → ret (s₁ + a + s₂)))
          (λ _ → ret triv))
      ≡⟨⟩
        step cost (1 , 1) (
          bind cost ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
            (λ _ → ret triv))
      ≤⟨ {!   !} ⟩
        step cost (1 , 1) (
          bind cost (bind cost (sum/seq _ _ _ t₁) (λ _ → ret triv) ∥ bind cost (sum/seq _ _ _ t₂) (λ _ → ret triv))
            (λ _ → ret triv))
      ≤⟨ ≤⁻-mono
          (λ e → step cost (1 , 1) (bind cost e (λ _ → ret triv)))
          (∥-mono-≤⁻ (sum/bounded' black n l₁ t₁) (sum/bounded' black n l₂ t₂)) ⟩
        step cost (1 , 1) (
          bind cost ((step⋆ (length l₁ , span/sum black n)) ∥ (step⋆ (length l₂ , span/sum black n)))
            (λ _ → ret triv))
      ≡⟨ Eq.cong (λ e → step cost (1 , 1) e)
          {x = bind cost
                ((step⋆ (length l₁ , span/sum black n)) ∥ (step⋆ (length l₂ , span/sum black n)))
              (λ _ → ret triv)}
          refl ⟩
        step cost (1 , 1) (
          step⋆ ((length l₁ , span/sum black n) ⊗ (length l₂ , span/sum black n)))
      ≡⟨ Eq.cong (λ c → step cost (1 , 1) (step⋆ c)) (Eq.cong₂ _,_ refl (Nat.⊔-idem (span/sum black n))) ⟩
        step cost (1 , 1) (
          step⋆ (length l₁ + length l₂ , span/sum black n))
      ≡⟨⟩
        step⋆ (1 + (length l₁ + length l₂) , 1 + 2 * n)
      ≡⟨ Eq.cong₂ (λ c₁ c₂ → step⋆ (c₁ , c₂)) (list/preserves/length l₁ a l₂) refl ⟩
        step⋆ (length l , span/sum red n)
      ∎
  sum/bounded' .black n@(suc n') l (black {y₁ = y₁} {y₂ = y₂} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        step cost (1 , 1) (
          bind cost (
            bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
              (λ (s₁ , s₂) → ret (s₁ + a + s₂)))
          (λ _ → ret triv))
      ≡⟨⟩
        step cost (1 , 1) (
          bind cost ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
            (λ _ → ret triv))
      ≤⟨ {!   !} ⟩
        step cost (1 , 1) (
          bind cost (bind cost (sum/seq _ _ _ t₁) (λ _ → ret triv) ∥ bind cost (sum/seq _ _ _ t₂) (λ _ → ret triv))
            (λ _ → ret triv))
      ≤⟨ ≤⁻-mono
          (λ e → step cost (1 , 1) (bind cost e (λ _ → ret triv)))
          (∥-mono-≤⁻  (sum/bounded' y₁ n' l₁ t₁) (sum/bounded' y₂ n' l₂ t₂)) ⟩
        step cost (1 , 1) (
          bind cost ((step⋆ (length l₁ , span/sum y₁ n')) ∥ (step⋆ (length l₂ , span/sum y₂ n')))
            (λ _ → ret triv))
      ≤⟨ ≤⁻-mono₂
          (λ e₁ e₂ → step cost (1 , 1) (bind cost (e₁ ∥ e₂) (λ _ → ret triv)))
            (step⋆-mono-≤⁻ (Nat.≤-refl {length l₁} , span/bounded y₁ n'))
            (step⋆-mono-≤⁻ (Nat.≤-refl {length l₂} , span/bounded y₂ n')) ⟩
        step cost (1 , 1) (
          bind cost ((step⋆ (length l₁ , 1 + 2 * n')) ∥ (step⋆ (length l₂ , 1 + 2 * n')))
            (λ _ → ret triv))
      ≡⟨ Eq.cong (λ e → step cost (1 , 1) e)
          {x = bind cost
                ((step⋆ (length l₁ , 1 + 2 * n')) ∥ (step⋆ (length l₂ , 1 + 2 * n')))
              (λ _ → ret triv)}
          refl ⟩
        step cost (1 , 1) (
          step⋆ ((length l₁ , 1 + 2 * n') ⊗ (length l₂ , 1 + 2 * n')))
      ≡⟨ Eq.cong (λ c → step cost (1 , 1) (step⋆ c)) (Eq.cong₂ _,_ refl (Nat.⊔-idem (1 + 2 * n'))) ⟩
        step cost (1 , 1) (
          step⋆ (length l₁ + length l₂ , 1 + 2 * n'))
      ≡⟨⟩
        step⋆ (1 + (length l₁ + length l₂) , 1 + (1 + 2 * n'))
      ≡⟨ Eq.cong₂ (λ c₁ c₂ → step⋆ (c₁ , c₂)) (list/preserves/length l₁ a l₂) (arithemtic n') ⟩
       step⋆ (length l , span/sum black n)
      ∎
        where
          arithemtic : ∀ n → 1 + (1 + 2 * n) ≡ 2 * (suc n)
          arithemtic n =
            let open ≡-Reasoning in
            begin
              1 + (1 + 2 * n)
            ≡⟨ Nat.+-assoc 1 1 (2 * n) ⟩
              (1 + 1) + 2 * n
            ≡⟨⟩
              2 + 2 * n
            ≡˘⟨ Nat.*-suc 2 n ⟩
              2 * (suc n)
            ∎

  sum/bounded : ∀ y n l t → IsBounded nat (sum/seq y n l t) (length l , 1 + 2 * ⌈log₂ (1 + length l) ⌉)
  sum/bounded y n l t =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (sum/seq y n l t) (λ _ → ret triv)
      ≤⟨ sum/bounded' y n l t ⟩
        step⋆ (length l , span/sum y n)
      ≤⟨ step⋆-mono-≤⁻ (Nat.≤-refl {length l} , lemma) ⟩
        step⋆ (length l , 1 + 2 * ⌈log₂ (1 + length l) ⌉)
      ∎
    where
      lemma : span/sum y n Nat.≤ 1 + (2 * ⌈log₂ (1 + length l) ⌉)
      lemma =
        let open Nat.≤-Reasoning in
        begin
          span/sum y n
        ≤⟨ span/bounded y n ⟩
          1 + (2 * n)
        ≤⟨ Nat.s≤s (Nat.*-monoʳ-≤ 2 (i-nodes/bound/log-node-black-height t)) ⟩
          1 + (2 * ⌈log₂ (1 + i-nodes t) ⌉)
        ≡⟨ Eq.cong (λ x → 1 + (2 * ⌈log₂ (1 + x) ⌉)) (i-nodes≡lengthl t) ⟩
          1 + (2 * ⌈log₂ (1 + length l) ⌉)
        ∎