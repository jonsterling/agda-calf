{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonad where

open Agda.Primitive
open import Agda.Builtin.Equality
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import CalfMonad.CostMonoid
open import CalfMonad.Monad

record CostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} (monad : Monad M) (costMonoid : CostMonoid ℂ) : Set (ℓ′ ⊔ ℓ″) where
  open Monad monad
  open CostMonoid costMonoid

  field
    step : ℂ → M ⊤

    step-𝟘 : step 𝟘 ≡ pure _
    step-⊕ : ∀ p q → step (p ⊕ q) ≡ step p >> step q

record ParCostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} {monad : Monad M} {costMonoid : CostMonoid ℂ} (costMonad : CostMonad monad costMonoid) (parCostMonoid : ParCostMonoid ℂ) : Set (lsuc ℓ ⊔ ℓ′ ⊔ ℓ″) where
  infix 5 _&_

  open Monad monad
  open CostMonad costMonad
  open ParCostMonoid parCostMonoid

  field
    _&_ : ∀ {A B} → M A → M B → M (A × B)

    step-pure-&-step-pure : ∀ {A B} p q a b → (step p >> pure {A} a) & (step q >> pure {B} b) ≡ step (p ⊗ q) >> pure (a , b)
