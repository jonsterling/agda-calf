{-# OPTIONS --rewriting #-}

-- The phase distinction for extension.

module Calf.Phase.Directed where

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Calf.Phase.Core
open import Calf.Phase.Open
open import Calf.Phase.Closed

postulate
  ≤⁺-ext-≡ : {a a' : val A} → ext → a ≤⁺[ A ] a' → a ≡ a'

≤⁻-ext-≡ : {e e' : cmp X} → ext → e ≤⁻[ X ] e' → e ≡ e'
≤⁻-ext-≡ = ≤⁺-ext-≡

fracture/decalf : {a a' : val A} →
  ◯ (a ≡ a') →
  η a ≤⁺[ ● A ] η a' →
  a ≤⁺[ A ] a'
fracture/decalf = {!   !}

open import Calf.Data.Product using (unit)
∥_∥ : cmp (F A) → cmp (F unit)
∥ e ∥ = bind (F unit) e λ _ → ret triv

fracture/decalf' : {e e' : cmp (F A)} →
  ◯ (e ≡ e') →
  ∥ e ∥ ≤⁻[ F unit ] ∥ e' ∥ →
  e ≤⁻[ F A ] e'
fracture/decalf' = {!   !}
