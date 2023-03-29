{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Types.Product where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Product using (_×_; _,_; proj₁; proj₂) public

prod⁺ : tp pos → tp pos → tp pos
prod⁺ A B = U (meta (val A × val B))
