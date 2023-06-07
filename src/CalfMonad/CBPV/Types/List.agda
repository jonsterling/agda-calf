{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.List {M : Set → Set} (monad : Monad M) where

open import Agda.Builtin.List using (List; []; _∷_) public

open import CalfMonad.CBPV monad

list : tp+ → tp+
list A = meta (List (val A))
