{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.MSequence where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid

-- Middle Sequence
record MSequence : Set where
  field
    seq : tp⁺ → tp⁺

    empty : cmp (F (seq A))
    join : cmp (Π (seq A) λ s₁ → Π A λ a → Π (seq A) λ s₂ → F (seq A))

    rec : {X : tp⁻} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (seq A) λ _ → Π (U X) λ _ → Π A λ _ → Π (seq A) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (seq A) λ _ → X
        )
