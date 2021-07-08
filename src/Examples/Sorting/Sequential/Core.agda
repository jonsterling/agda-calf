{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.Core (M : Comparable) where

open import Examples.Sorting.Core costMonoid fromℕ M public
