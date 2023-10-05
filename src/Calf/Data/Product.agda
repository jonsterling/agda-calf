{-# OPTIONS --rewriting #-}

module Calf.Data.Product where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality using (_≡_)

-- definitions exported by CBPV.agda are hidden
open import Data.Unit public renaming (⊤ to Unit) hiding (tt)
open import Data.Product hiding (_,_; proj₁; proj₂) public

unit : tp⁺
unit = meta⁺ Unit

infixr 2 _×⁺_
_×⁺_ : tp⁺ → tp⁺ → tp⁺
A ×⁺ B = meta⁺ (val A × val B)
