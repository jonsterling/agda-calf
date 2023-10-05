{-# OPTIONS --rewriting #-}

module Calf.Data.Nat where

open import Calf.Prelude
open import Calf.CBPV

open import Data.Nat public

nat : tp⁺
nat = meta⁺ ℕ
