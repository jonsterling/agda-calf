{-# OPTIONS --prop --rewriting #-}

open import Calf.Metalanguage
open import Examples.Sequence.MSequence

module Examples.Sequence.DerivedForms (MSeq : MSequence) where

open MSequence MSeq


append : cmp (Π (seq A) λ _ → Π (seq A) λ _ → F (seq A))
append {A} s₁ s₂ =
  rec {X = F (seq A)}
    (ret s₂)
    (λ s₁ _ a _ ih →
      bind (F (seq A)) ih λ s₂ →
      join s₁ a s₂)
    s₁
