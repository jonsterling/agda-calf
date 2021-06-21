{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf (costMonoid : CostMonoid) where

orderedMonoid = CostMonoid.orderedMonoid costMonoid
monoid = OrderedMonoid.monoid orderedMonoid

open import Calf.Prelude hiding (_≡_; refl) public
open import Calf.Metalanguage public
open import Calf.Step monoid public
open import Calf.CostEffect orderedMonoid public
open import Calf.PhaseDistinction orderedMonoid public
open import Calf.Eq public
open import Calf.Upper orderedMonoid public
open import Calf.Connectives orderedMonoid public

open import Calf.Refinement costMonoid public
