{-# OPTIONS --cubical-compatible --rewriting #-}

module CalfNew.Types.Sigma where

open import Agda.Builtin.Sigma public
open import CalfNew.Metalanguage

Σ′ : ∀ A → (val A → tp+) → tp+
Σ′ A B = meta (Σ (val A) λ a → val (B a))

infixr 2 Σ′
syntax Σ′ A (λ _ → B) = A ×′ B
