{-# OPTIONS --without-K #-}

module Calf.Types.Unit where

open import Calf.Prelude
open import Calf.Metalanguage
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Unit public using (⊤) renaming (tt to triv)


postulate
  unit : tp pos
  unit/decode : val unit ≡ ⊤
  {-# REWRITE unit/decode #-}

postulate
  unit⁻ : tp neg
  unit⁻/decode : val (U unit⁻) ≡ ⊤
  {-# REWRITE unit⁻/decode #-}
