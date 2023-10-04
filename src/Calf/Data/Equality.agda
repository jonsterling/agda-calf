{-# OPTIONS --rewriting #-}

module Calf.Data.Equality where

open import Calf.Prelude
open import Calf.CBPV

open import Relation.Binary.PropositionalEquality public

_≡⁺_ : val A → val A → tp pos
a ≡⁺ a' = meta⁺ (a ≡ a')

≡⁺-syntax : val A → val A → tp pos
≡⁺-syntax {A} = _≡⁺_ {A}

syntax ≡⁺-syntax {A} a a' = a ≡⁺[ A ] a'
