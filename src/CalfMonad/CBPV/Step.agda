{-# OPTIONS --cubical-compatible --lossy-unification --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad

module CalfMonad.CBPV.Step {ℓ ℓ′} {M : Set ℓ → Set ℓ} {ℂ : Set ℓ′} {monad : Monad M} {costMonoid : CostMonoid ℂ} (costMonad : CostMonad monad costMonoid) where

open CostMonoid costMonoid

open import Agda.Builtin.Equality

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Types.Unit monad

step : ℂ → cmp (F unit)
step = CostMonad.step costMonad

step-𝟘 : step 𝟘 ≡ ret _
step-𝟘 = CostMonad.step-𝟘 costMonad

step-⊕ : ∀ p q → step (p ⊕ q) ≡ bind (step p) λ _ → step q
step-⊕ = CostMonad.step-⊕ costMonad
