{-# OPTIONS --rewriting #-}

module Calf.Data.Equality where

open import Calf.Prelude
open import Calf.CBPV

open import Relation.Binary.PropositionalEquality public

_≡⁺_ : val A → val A → tp pos
a ≡⁺ a' = meta⁺ (a ≡ a')

infix 4 ≡⁺-syntax
≡⁺-syntax : val A → val A → tp pos
≡⁺-syntax {A} = _≡⁺_ {A}

syntax ≡⁺-syntax {A} a a' = a ≡⁺[ A ] a'


postulate
  _≡⁻_ : cmp X → cmp X → tp neg
  ≡⁻/decode : {e e' : cmp X} → val (U (_≡⁻_ {X} e e')) ≡ val (_≡⁺_ {U X} e e')
  {-# REWRITE ≡⁻/decode #-}

infix 4 ≡⁻-syntax
≡⁻-syntax : cmp X → cmp X → tp neg
≡⁻-syntax {X} = _≡⁻_ {X}

syntax ≡⁻-syntax {X} e e' = e ≡⁻[ X ] e'
