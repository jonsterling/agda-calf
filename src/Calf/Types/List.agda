{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.List where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.List public using (List; []; _∷_; [_]; length; _++_)
open import Data.List.Properties public

list : tp pos → tp pos
list A = U (meta (List (val A)))
