{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Types.Product where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Product using (_×_; _,_; proj₁; proj₂) public

prod⁺ : tp pos → tp pos → tp pos
prod⁺ A B = U (meta (val A × val B))

-- Doesn't seem to work?
-- prod⁻ : tp neg → tp neg → tp neg
-- prod⁻ X Y = meta (cmp X × cmp Y)

record Prod⁻ (X Y : tp neg) : Set where
  constructor _,_
  field
    proj₁ : cmp X
    proj₂ : cmp Y
open Prod⁻ public

prod⁻ : tp neg → tp neg → tp neg
prod⁻ X Y = meta (Prod⁻ X Y)
