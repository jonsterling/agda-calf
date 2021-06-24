{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude hiding (_≡_; refl) public
open import Calf.Metalanguage public
open import Calf.Step costMonoid public
open import Calf.PhaseDistinction costMonoid public
open import Calf.Eq public
open import Calf.Upper costMonoid public
open import Calf.BoundedFunction costMonoid public
open import Calf.Refinement costMonoid public

open import Calf.CostEffect public
