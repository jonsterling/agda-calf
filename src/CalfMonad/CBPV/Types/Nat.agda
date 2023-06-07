{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.Nat {M : Set → Set} (monad : Monad M) where

open import Agda.Builtin.Nat using (Nat; zero; suc) public

open import CalfMonad.CBPV monad

nat : tp+
nat = meta Nat
