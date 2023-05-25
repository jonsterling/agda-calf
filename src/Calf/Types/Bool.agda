{-# OPTIONS --cubical-compatible --prop --rewriting #-}

module Calf.Types.Bool where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Bool public using (Bool; true; false; if_then_else_)

bool : tp pos
bool = U (meta Bool)
