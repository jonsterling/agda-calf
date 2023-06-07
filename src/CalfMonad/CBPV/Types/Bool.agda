{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.Bool {M : Set → Set} (monad : Monad M) where

open import Agda.Builtin.Bool using (Bool; false; true) public

open import CalfMonad.CBPV monad

bool : tp+
bool = meta Bool
