{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Types.Sigma {ℓ} {M : Set ℓ → Set ℓ} (monad : Monad M) where

open import Agda.Builtin.Sigma using (Σ; _,_) public

open import CalfMonad.CBPV monad

Σ′ : ∀ A → (val A → tp+) → tp+
Σ′ A B = meta (Σ (val A) λ a → val (B a))

infixr 2 Σ′
syntax Σ′ A (λ _ → B) = A ×′ B
