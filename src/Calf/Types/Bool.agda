{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Types.Bool where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Bool public using (Bool; true; false)

bool : tp pos
bool = meta Bool
