{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Types.List where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.List public using (List; []; _∷_; _∷ʳ_; [_]; length; _++_)
open import Data.List.Properties public

list : tp pos → tp pos
list A = U (meta (List (val A)))
