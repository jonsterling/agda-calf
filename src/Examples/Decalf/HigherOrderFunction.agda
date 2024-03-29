{-# OPTIONS --rewriting #-}

module Examples.Decalf.HigherOrderFunction where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Nat as Nat using (nat; zero; suc; _+_; _*_)
import Data.Nat.Properties as Nat
open import Data.Nat.Square
open import Calf.Data.List using (list; []; _∷_; [_]; _++_; length)
open import Calf.Data.Bool using (bool; if_then_else_)
open import Calf.Data.Product using (unit)
open import Calf.Data.Equality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.IsBounded costMonoid
open import Function


module Twice where
  twice : cmp $ Π (U (F nat)) λ _ → F nat
  twice e =
    bind (F nat) e λ x₁ →
    bind (F nat) e λ x₂ →
    ret (x₁ + x₂)

  twice/is-bounded : (e : cmp (F nat)) → IsBounded nat e 1 → IsBounded nat (twice e) 2
  twice/is-bounded e e≤step⋆1 =
    let open ≤⁻-Reasoning cost in
    begin
      bind cost
        ( bind (F nat) e λ x₁ →
          bind (F nat) e λ x₂ →
          ret (x₁ + x₂)
        )
        (λ _ → ret triv)
    ≡⟨⟩
      ( bind cost e λ _ →
        bind cost e λ _ →
        ret triv
      )
    ≲⟨ ≤⁻-mono₂ (λ e₁ e₂ → bind (F _) e₁ λ _ → bind (F _) e₂ λ _ → ret triv) e≤step⋆1 e≤step⋆1 ⟩
      ( bind cost (step⋆ 1) λ _ →
        bind cost (step⋆ 1) λ _ →
        ret triv
      )
    ≡⟨⟩
      step⋆ 2
    ∎

module Map where
  map : cmp $ Π (U (Π nat λ _ → F nat)) λ _ → Π (list nat) λ _ → F (list nat)
  map f []       = ret []
  map f (x ∷ xs) =
    bind (F (list nat)) (f x) λ y →
    bind (F (list nat)) (map f xs) λ ys →
    ret (y ∷ ys)

  map/is-bounded :
    (f : cmp (Π nat λ _ → F nat)) →
    ((x : val nat) → IsBounded nat (f x) c) →
    (l : val (list nat)) →
    IsBounded (list nat) (map f l) (length l * c)
  map/is-bounded     f f-bound []       = ≤⁻-refl
  map/is-bounded {c} f f-bound (x ∷ xs) =
    let open ≤⁻-Reasoning cost in
    begin
      bind cost
        ( bind (F (list nat)) (f x) λ y →
          bind (F (list nat)) (map f xs) λ ys →
          ret (y ∷ ys)
        )
        (λ _ → ret triv)
    ≡⟨⟩
      ( bind cost (f x) λ _ →
        bind cost (map f xs) λ _ →
        ret triv
      )
    ≲⟨
      ≤⁻-mono₂ (λ e₁ e₂ → bind cost e₁ λ _ → bind cost e₂ λ _ → ret triv)
        (f-bound x)
        (map/is-bounded f f-bound xs)
    ⟩
      ( bind cost (step⋆ c) λ _ →
        bind cost (step⋆ (length xs * c)) λ _ →
        ret triv
      )
    ≡⟨⟩
      step⋆ (length (x ∷ xs) * c)
    ∎

  open import Examples.Decalf.ProbabilisticChoice
  map/is-bounded' :
    (f : cmp (Π nat λ _ → F nat)) →
    {n : val nat} →
    ((x : val nat) → IsBoundedG nat (f x) (binomial n)) →
    (l : val (list nat)) →
    IsBoundedG (list nat) (map f l) (binomial (length l * n))
  map/is-bounded' f {n} f-bound []       = ≤⁻-refl
  map/is-bounded' f {n} f-bound (x ∷ xs) =
    let open ≤⁻-Reasoning cost in
    begin
      bind cost
        ( bind (F (list nat)) (f x) λ y →
          bind (F (list nat)) (map f xs) λ ys →
          ret (y ∷ ys)
        )
        (λ _ → ret triv)
    ≡⟨⟩
      ( bind cost (f x) λ _ →
        bind cost (map f xs) λ _ →
        ret triv
      )
    ≲⟨ ≤⁻-mono (λ e → bind cost (f x) λ _ → e) (map/is-bounded' f f-bound xs) ⟩
      ( bind cost (f x) λ _ →
        binomial (length xs * n)
      )
    ≲⟨ ≤⁻-mono (λ e → bind cost e λ _ → binomial (length xs * n)) (f-bound x) ⟩
      ( bind cost (binomial n) λ _ →
        binomial (length xs * n)
      )
    ≡⟨ binomial/+ n (length xs * n) ⟩
      binomial (n + length xs * n)
    ≡⟨⟩
      binomial (length (x ∷ xs) * n)
    ∎
