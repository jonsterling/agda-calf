{-# OPTIONS --cubical-compatible --prop --rewriting #-}

module Examples.Sequence.ArraySig where

open import Calf.Metalanguage
open import Calf.Types.Bool
open import Calf.Types.Fin
open import Calf.Types.Nat
open import Calf.Types.Vec

open import Data.Bool        using (_∨_)
open import Data.Fin         using (_≟_)
open import Data.Vec         using (lookup; tabulate)
open import Relation.Nullary using (does)

private variable A : tp pos

record ARRAY : Set where
  field
    array  : (A : tp pos) (n : val nat)                        → tp pos
    update : (A : tp pos) (n : val nat) (m : val (vec bool n)) → tp pos

    nth    : cmp (Π nat         λ n  →
                  Π (array A n) λ as →
                  Π (fin n)     λ i  →
                  F A)

    nil    : cmp (Π nat λ n →
                  F (update A n (tabulate λ i → false)))

    assign : cmp (Π nat     λ n →
                  Π (fin n) λ i →
                  Π A       λ a →
                  F (update A n (tabulate λ j → does (i ≟ j))))

    join   : cmp (Π nat             λ n  →
                  Π (vec bool n)    λ m₁ →
                  Π (update A n m₁) λ u₁ →
                  Π (vec bool n)    λ m₂ →
                  Π (update A n m₂) λ u₂ →
                  F (update A n (tabulate λ i → lookup m₁ i ∨ lookup m₂ i)))

    mk     : cmp (Π nat                                        λ n →
                  Π (U (F (update A n (tabulate λ i → true)))) λ u →
                  F (array A n))
