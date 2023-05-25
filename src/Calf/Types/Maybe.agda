{-# OPTIONS --cubical-compatible --prop --rewriting #-}

module Calf.Types.Maybe where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Maybe public using (Maybe; just; nothing)

maybe : tp pos → tp pos
maybe A = U (meta (Maybe (val A)))
