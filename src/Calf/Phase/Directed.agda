{-# OPTIONS --rewriting #-}

-- The phase distinction for extension.

module Calf.Phase.Directed where

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Calf.Phase.Core

postulate
  ≲-ext-≡ : {X : tp neg} {e₁ e₂ : cmp X} → ext → e₁ ≲[ X ] e₂ → e₁ ≡ e₂
