{-# OPTIONS --prop --rewriting #-}

open import Examples.Sorting.Parallel.Comparable

module Examples.Sorting.Parallel.Core (M : Comparable) where

open import Examples.Sorting.Core costMonoid fromℕ M public
