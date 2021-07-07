{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude public
open import Calf.Metalanguage public
open import Calf.PhaseDistinction public
open import Calf.Noninterference public
open import Calf.Step costMonoid public
