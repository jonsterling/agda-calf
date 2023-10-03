{-# OPTIONS --rewriting #-}

open import Algebra.Cost

module Calf.Types.Eq where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality


eq : (A : tp pos) → val A → val A → tp pos
eq A a a' = meta⁺ (a ≡ a')
