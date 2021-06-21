{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Types.Sum where

open import Calf.Prelude
open import Calf.Metalanguage

open import Data.Sum using (_⊎_; inj₁; inj₂) public

sum : tp pos → tp pos → tp pos
sum A B = U (meta (val A ⊎ val B))

sum/case : ∀ A B (X : val (sum A B) → tp neg) → (s : val (sum A B)) → ((a : val A) → cmp (X (inj₁ a))) → ((b : val B) → cmp (X (inj₂ b))) → cmp (X s)
sum/case A B X (inj₁ x) b₁ _  = b₁ x
sum/case A B X (inj₂ x) _  b₂ = b₂ x
