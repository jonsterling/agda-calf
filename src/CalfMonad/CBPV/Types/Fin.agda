{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.Fin {M : Set → Set} (monad : Monad M) where

open import Data.Fin.Base using (Fin; zero; suc) public

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Types.Nat monad

fin : val nat → tp+
fin n = meta (Fin n)
