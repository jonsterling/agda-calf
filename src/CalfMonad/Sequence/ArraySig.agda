{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.Sequence.ArraySig {M} (monad : Monad M) where

open import Agda.Builtin.Nat
open import Data.Bool.Base      using (Bool; _∨_; false; true)
open import Data.Fin.Base       using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Vec.Base       using (Vec; lookup; tabulate)
open import Relation.Nullary    using (does)

open import CalfMonad.CBPV monad

private
  variable
    A : tp+
    n : Nat

record ARRAY : Set₁ where
  field
    Array        : (A : tp+) (n : Nat)                  → tp+
    ArrayBuilder : (A : tp+) (n : Nat) (m : Vec Bool n) → tp-

    nth : (as : Array A n) (i : Fin n) → M A

    empty : U (ArrayBuilder A n (tabulate λ i → false))

    assign : (i : Fin n) (a : A) → U (ArrayBuilder A n (tabulate λ j → does (i ≟ j)))

    seq : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → U (ArrayBuilder A n (tabulate λ i → lookup m₂ i ∨ lookup m₁ i))

    par : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → U (ArrayBuilder A n (tabulate λ i → lookup m₁ i ∨ lookup m₂ i))

    build : (b : U (ArrayBuilder A n (tabulate λ i → true))) → M (Array A n)
