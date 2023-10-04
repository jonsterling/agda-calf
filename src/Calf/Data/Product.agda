{-# OPTIONS --rewriting #-}

module Calf.Data.Product where

open import Calf.Prelude
open import Calf.CBPV
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Unit public renaming (⊤ to Unit; tt to triv)
open import Data.Product public

unit : tp pos
unit = meta⁺ Unit

infixr 2 _×⁺_
_×⁺_ : tp pos → tp pos → tp pos
A ×⁺ B = meta⁺ (val A × val B)
