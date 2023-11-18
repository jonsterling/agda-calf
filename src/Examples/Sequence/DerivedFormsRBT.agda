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
-- open import Calf.Data.Sum
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid
-- open import Data.Product hiding (map)
-- open import Data.List as List hiding (sum; map)
-- import Data.List.Properties as List
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _∸_)
import Data.Nat.Properties as Nat
-- open import Data.Nat.Logarithm

open import Level using (0ℓ)
open import Function using (_$_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)

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
      ≤⟨ ≤⁻-mono (λ e →
          bind cost
            ((mapreduce _ _ _ t₁ f g z) ∥ (mapreduce _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ s₃ →
                  bind cost e λ _ →
                    ret triv) {! g-bound  !} ⟩
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
