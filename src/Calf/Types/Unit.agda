{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.Unit (costMonoid : CostMonoid) where

open import Calf.Prelude
open import Calf.Metalanguage costMonoid

open import Data.Unit public using (⊤) renaming (tt to triv)

postulate
  unit : tp pos
  unit/decode : val unit ≡ ⊤
  {-# REWRITE unit/decode #-}
