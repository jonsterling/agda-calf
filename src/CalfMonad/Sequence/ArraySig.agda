{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.ArraySig {ℓ ℓ′} (M : Set ℓ → Set ℓ′) where

open Agda.Primitive
open import Data.Bool.Base   using (Bool; false; true; _∨_)
open import Data.Fin         using (_≟_)
open import Data.Fin.Base    using (Fin)
open import Data.Nat.Base    using (ℕ)
open import Data.Vec.Base    using (Vec; lookup; tabulate)
open import Relation.Nullary using (does)

private
  variable
    A : Set ℓ
    n : ℕ
    S : Set

record ARRAY : Set (lsuc ℓ ⊔ ℓ′) where
  field
    Array        : (A : Set ℓ) (n : ℕ)                            → Set ℓ
    ArrayBuilder : (A : Set ℓ) (n : ℕ) (S : Set) (m : Vec Bool n) → Set ℓ

    nth : (as : Array A n) (i : Fin n) → M A

    empty : M (ArrayBuilder A n S (tabulate λ i → false))

    assign : (i : Fin n) (a : A) → M (ArrayBuilder A n S (tabulate λ j → does (i ≟ j)))

    join : ∀ {m₁} (b₁ : ArrayBuilder A n S m₁) {m₂} (b₂ : ArrayBuilder A n S m₂) → M (ArrayBuilder A n S (tabulate λ i → lookup m₁ i ∨ lookup m₂ i))

    build : (b : ∀ {S} → M (ArrayBuilder A n S (tabulate λ i → true))) → M (Array A n)
