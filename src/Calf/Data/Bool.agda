{-# OPTIONS --rewriting #-}

module Calf.Data.Bool where

open import Calf.Prelude
open import Calf.CBPV

open import Data.Bool public

bool : tp pos
bool = meta⁺ Bool
