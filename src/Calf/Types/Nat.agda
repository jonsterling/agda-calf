{-# OPTIONS --without-K --prop --rewriting #-}

module Calf.Types.Nat where

open import Calf.Prelude
open import Calf.Metalanguage
open import Data.Nat

nat : tp pos
nat = U (meta ℕ)
