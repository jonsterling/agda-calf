{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonad ℓ ℓ′ ℓ″ where

open Agda.Primitive
open import Agda.Builtin.Equality
open import Data.Product using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import CalfMonad.CostMonoid ℓ
open import CalfMonad.Monad ℓ′ ℓ″

record CostMonad (costMonoid : CostMonoid) : Set (ℓ ⊔ lsuc (ℓ′ ⊔ ℓ″)) where
  open CostMonoid costMonoid

  field
    monad : Monad

  open Monad monad public

  field
    step : ℂ → M ⊤

    step-𝟘 : step 𝟘 ≡ pure tt
    step-⊕ : ∀ p q → step (p ⊕ q) ≡ step p >> step q

record ParCostMonad (parCostMonoid : ParCostMonoid) : Set (ℓ ⊔ lsuc (ℓ′ ⊔ ℓ″)) where
  infixr 5 _&_

  open ParCostMonoid parCostMonoid

  field
    costMonad : CostMonad costMonoid

  open CostMonad costMonad public

  field
    _&_ : ∀ {A B} → M A → M B → M (A × B)

    step-pure-&-step-pure : ∀ {A B} p q a b → step p >> pure {A} a & step q >> pure {B} b ≡ step (p ⊗ q) >> pure (a , b)
