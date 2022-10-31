{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Nat
open import Calf.Types.Bounded costMonoid

open import Function

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)



import Algebra.Structures as A

variable
  A B C : tp pos
  X Y Z : tp neg

_≅_ : cmp X → cmp X → Set
x ≅ y = ◯ (x ≡ y)

lift₁ : cmp (Π A λ _ → X) → cmp (Π (U (F A)) λ _ → X)
lift₁ {X = X} f e = bind X e f

lift₂ : cmp (Π A λ _ → Π B λ _ → X) → cmp (Π (U (F A)) λ _ → Π (U (F B)) λ _ → X)
lift₂ {X = X} f e₁ e₂ = bind X e₁ λ v₁ → bind X e₂ λ v₂ → f v₁ v₂

record SEQUENCE_CORE : Set₁ where
  field
    Seq : tp pos → tp pos

    singleton : cmp (Π A λ _ → F (Seq A))
    empty : cmp (F (Seq A))
    append : cmp (Π (Seq A) λ _ → Π (Seq A) λ _ → F (Seq A))
    isMonoid : A.IsMonoid (_≅_ {F (Seq A)}) (lift₂ {X = F (Seq A)} append) empty

    mapreduce :
      cmp (Π A λ _ → X)
      → (z : cmp X)
      → (g : cmp (Π (U X) λ _ → Π (U X) λ _ → X))
      → A.IsMonoid (_≅_ {X}) g z
      → val (Seq A)
      → cmp X
    mapreduce/singleton : ∀ {f z g h a}     → ◯ (lift₁ {X = X} (mapreduce {X = X} f z g h) (singleton {A} a ) ≡ f a)
    mapreduce/empty     : ∀ {f z g h}       → ◯ (lift₁ {X = X} (mapreduce {X = X} f z g h) (empty {A}       ) ≡ z)
    mapreduce/append    : ∀ {f z g h s₁ s₂} → ◯ (lift₁ {X = X} (mapreduce {X = X} f z g h) (append {A} s₁ s₂) ≡ g (mapreduce {X = X} f z g h s₁) (mapreduce {X = X} f z g h s₂))
    -- induction :
    --   {P : cmp (F (Seq A)) → Set}
    --   → (∀ a → P (singleton a))
    --   → P empty
    --   → (∀ s₁ s₂ → P s₁ → P s₂ → {!   !} P (append s₁ s₂))
    --   → val (Seq A)
    --   → cmp (F B)

module Foo (S : SEQUENCE_CORE) where
  open SEQUENCE_CORE S

  map : cmp (Π (U (Π A λ _ → F B)) λ _ → Π (Seq A) λ _ → F (Seq B))
  map {B = B} f =
    mapreduce {X = F (Seq B)}
      (lift₁ {X = F (Seq B)} singleton ∘ f)
      empty
      (lift₂ {X = F (Seq B)} append)
      (isMonoid S)

  reverse : cmp (Π (Seq A) λ _ → F (Seq A))
  reverse {A = A} =
    mapreduce {X = F (Seq A)}
      singleton
      empty
      (λ s₁ s₂ → lift₂ {X = F (Seq A)} append s₂ s₁)
      {!   !}

  example : (f : cmp (Π A λ _ → F B)) (s : val (Seq A)) → lift₁ {X = F (Seq B)} (map f) (reverse s) ≡ lift₁ {X = F (Seq B)} reverse (map f s)
  example f s = {!   !}
