{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf (CostMonoid : CostMonoid) where

open import Calf.Prelude hiding (_≡_; refl) public
open import Calf.Metalanguage CostMonoid public
open import Calf.CostEffect CostMonoid public
open import Calf.PhaseDistinction CostMonoid public
open import Calf.Eq CostMonoid public
open import Calf.Upper CostMonoid public
open import Calf.Connectives CostMonoid public

open import Calf.Refinement CostMonoid public
