{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.Sequence.ArraySig {M : Set → Set} (monad : Monad M) where

open import Data.Bool.Base      using (_∨_)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base       using (lookup; tabulate)
open import Relation.Nullary    using (does)

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Types.Bool monad
open import CalfMonad.CBPV.Types.Fin monad
open import CalfMonad.CBPV.Types.Nat monad
open import CalfMonad.CBPV.Types.Vec monad

private
  variable
    A : tp+

record ARRAY : Set₁ where
  field
    array        : (A : tp+) (n : val nat)                        → tp+
    arrayBuilder : (A : tp+) (n : val nat) (m : val (vec bool n)) → tp-

    nth : cmp (Π nat         λ n  →
               Π (array A n) λ as →
               Π (fin n)     λ i  →
               F A)

    empty : cmp (Π nat λ n →
                 arrayBuilder A n (tabulate λ i → false))

    assign : cmp (Π nat     λ n →
                  Π (fin n) λ i →
                  Π A       λ a →
                  arrayBuilder A n (tabulate λ j → does (i ≟ j)))

    seq : cmp (Π nat                       λ n  →
               Π (vec bool n)              λ m₁ →
               Π (U (arrayBuilder A n m₁)) λ b₁ →
               Π (vec bool n)              λ m₂ →
               Π (U (arrayBuilder A n m₂)) λ b₂ →
               arrayBuilder A n (tabulate λ i → lookup m₂ i ∨ lookup m₁ i))

    par : cmp (Π nat                       λ n  →
               Π (vec bool n)              λ m₁ →
               Π (U (arrayBuilder A n m₁)) λ b₁ →
               Π (vec bool n)              λ m₂ →
               Π (U (arrayBuilder A n m₂)) λ b₂ →
               arrayBuilder A n (tabulate λ i → lookup m₁ i ∨ lookup m₂ i))

    build : cmp (Π nat                                          λ n →
                 Π (U (arrayBuilder A n (tabulate λ i → true))) λ b →
                 F (array A n))
