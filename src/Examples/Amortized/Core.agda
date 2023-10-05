{-# OPTIONS --rewriting #-}

module Examples.Amortized.Core where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Product


infix 3 _⇒_ _⇔_
_⇒_ _⇔_ : tp pos → tp pos → tp pos
A ⇒ B = meta⁺ (val A → val B)
A ⇔ B = (A ⇒ B) ×⁺ (B ⇒ A)
