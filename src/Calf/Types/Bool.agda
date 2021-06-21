{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.Bool (costMonoid : CostMonoid) where

open import Calf.Prelude
open import Calf.Metalanguage costMonoid

open import Data.Bool public using (Bool; true; false)

bool : tp pos
bool = U (meta Bool)
