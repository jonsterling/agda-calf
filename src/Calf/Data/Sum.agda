{-# OPTIONS --rewriting #-}

module Calf.Data.Sum where

open import Calf.Prelude
open import Calf.CBPV

open import Data.Sum public

_⊎⁺_ : tp⁺ → tp⁺ → tp⁺
A ⊎⁺ B = meta⁺ (val A ⊎ val B)
