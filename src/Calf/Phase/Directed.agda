{-# OPTIONS --rewriting #-}

-- The phase distinction for extension.

module Calf.Phase.Directed where

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Calf.Phase.Core

postulate
  ≤⁺-ext-≡ : {a a' : val A} → ext → a ≤⁺[ A ] a' → a ≡ a'

≤⁻-ext-≡ : {e e' : cmp X} → ext → e ≤⁻[ X ] e' → e ≡ e'
≤⁻-ext-≡ = ≤⁺-ext-≡
