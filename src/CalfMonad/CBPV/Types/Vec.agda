{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.Vec {M : Set → Set} (monad : Monad M) where

open import Data.Vec.Base using (Vec; []; _∷_) public

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Types.Nat monad

vec : tp+ → val nat → tp+
vec A n = meta (Vec (val A) n)
