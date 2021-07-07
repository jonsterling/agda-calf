{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude public
open import Calf.Metalanguage public
open import Calf.PhaseDistinction public
open import Calf.Eq public

open import Calf.Step costMonoid public
open import Calf.ExtensionalFragment costMonoid public

open import Calf.Bounded costMonoid public
open import Calf.BoundedFunction costMonoid public
