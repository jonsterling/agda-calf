{-# OPTIONS --prop --without-K --rewriting #-}

module Calf.Types.Fin where

open import Calf.Metalanguage
open import Calf.Types.Nat

open import Data.Fin.Base public using (Fin; zero; suc)

fin : val nat → tp pos
fin n = U (meta (Fin n))
