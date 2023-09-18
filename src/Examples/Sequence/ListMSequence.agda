{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.ListMSequence where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Types.List
open import Calf.Types.Product
open import Data.Nat as Nat using (_+_)


open import Examples.Sequence.MSequence


ListMSequence : MSequence
ListMSequence =
  record
    { seq = list
    ; empty = ret []
    ; join =
        λ {A} l₁ a l₂ →
          let n = length l₁ + 1 + length l₂ in
          step (F (list A)) (n , n) (ret (l₁ ++ [ a ] ++ l₂))
    ; rec = λ {A} {X} → rec {A} {X}
    }
  where
    rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (list A) λ _ → Π (U X) λ _ → Π A λ _ → Π (list A) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (list A) λ _ → X
        )
    rec {A} {X} z f []      = z
    rec {A} {X} z f (x ∷ l) = step X (1 , 1) (f [] z x l (rec {A} {X} z f l))
