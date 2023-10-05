{-# OPTIONS --rewriting #-}

module Calf.Data.List where

open import Calf.Prelude
open import Calf.CBPV

open import Data.List public

list : tp⁺ → tp⁺
list A = meta⁺ (List (val A))
