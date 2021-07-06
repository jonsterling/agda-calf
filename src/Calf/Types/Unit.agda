{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Types.Unit where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Unit public using (⊤) renaming (tt to triv)

unit : tp pos
unit = meta ⊤
