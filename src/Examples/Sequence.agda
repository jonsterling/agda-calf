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

lift₁ : cmp (Π A λ _ → F C) → cmp (Π (U (F A)) λ _ → F C)
lift₁ {C = C} f e = bind (F C) e f

lift₂ : cmp (Π A λ _ → Π B λ _ → F C) → cmp (Π (U (F A)) λ _ → Π (U (F B)) λ _ → F C)
lift₂ {C = C} f e₁ e₂ = bind (F C) e₁ λ v₁ → bind (F C) e₂ λ v₂ → f v₁ v₂

record SEQUENCE_CORE : Set₁ where
  field
    Seq : tp pos → tp pos

    singleton : cmp (Π A λ _ → F (Seq A))
    empty : cmp (F (Seq A))
    append : cmp (Π (Seq A) λ _ → Π (Seq A) λ _ → F (Seq A))
    isMonoid : A.IsMonoid (_≅_ {F (Seq A)}) (lift₂ append) empty

    mapreduce :
      cmp (Π A λ _ → F B)
      → cmp (F B)
      → cmp (Π B λ _ → Π B λ _ → F B)
      → val (Seq A)
      → cmp (F B)
    mapreduce/singleton : ∀ {f z g a}     → ◯ (lift₁ {C = B} (mapreduce f z g) (singleton {A} a ) ≡ f a)
    mapreduce/empty     : ∀ {f z g}       → ◯ (lift₁ {C = B} (mapreduce f z g) (empty {A}       ) ≡ z)
    mapreduce/append    : ∀ {f z g s₁ s₂} → ◯ (lift₁ {C = B} (mapreduce f z g) (append {A} s₁ s₂) ≡ lift₂ g (mapreduce f z g s₁) (mapreduce f z g s₂))
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
  map f = mapreduce (lift₁ singleton ∘ f) empty append

  reverse : cmp (Π (Seq A) λ _ → F (Seq A))
  reverse = mapreduce singleton empty (λ s₁ s₂ → append s₂ s₁)

  example : (f : cmp (Π A λ _ → F B)) (s : val (Seq A)) → lift₁ (map f) (reverse s) ≡ lift₁ reverse (map f s)
  example f s = {!   !}
