{-# OPTIONS --without-K #-}

module Calf.Types.Product where

open import Calf.Prelude
open import Calf.Metalanguage
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Product using (_×_; _,_; proj₁; proj₂) public

postulate
  prod⁺ : tp pos → tp pos → tp pos
  prod⁺/decode : {A B : tp pos} → val (prod⁺ A B) ≡ (val A × val B)
  {-# REWRITE prod⁺/decode #-}

postulate
  prod⁻ : tp neg → tp neg → tp neg
  prod⁻/decode : {X Y : tp neg} → val (U (prod⁻ X Y)) ≡ (cmp X × cmp Y)
  {-# REWRITE prod⁻/decode #-}
