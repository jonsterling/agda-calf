{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonad where

open Agda.Primitive
open import Data.Product                               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base                 using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong; sym; trans)

open import CalfMonad.CostMonoid
open import CalfMonad.Monad

record CostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} (monad : Monad M) (costMonoid : CostMonoid ℂ) : Set (ℓ′ ⊔ ℓ″) where
  open Monad monad
  open CostMonoid costMonoid

  field
    step : ℂ → M ⊤

    step-𝟘 : step 𝟘 ≡ pure _
    step-⊕ : ∀ p q → step (p ⊕ q) ≡ step p >> step q

  step-𝟘->> : ∀ {A} (x : M A) → step 𝟘 >> x ≡ x
  step-𝟘->> x = trans (cong (_>>= _) step-𝟘) (pure->>= _ _)

  ext : Set (ℓ′ ⊔ ℓ″)
  ext = ∀ p → step p ≡ pure _

  ext/step->> : ext → ∀ {A} p (x : M A) → step p >> x ≡ x
  ext/step->> u p x = trans (cong (_>>= _) (u p)) (pure->>= _ _)

record ParCostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} {monad : Monad M} {costMonoid : CostMonoid ℂ} (costMonad : CostMonad monad costMonoid) (parCostMonoid : ParCostMonoid ℂ) : Set (lsuc ℓ ⊔ ℓ′ ⊔ ℓ″) where
  infix 5 _&_

  open Monad monad
  open CostMonoid costMonoid
  open CostMonad costMonad
  open ParCostMonoid parCostMonoid

  field
    _&_ : ∀ {A B} → M A → M B → M (A × B)

    step-pure-&-step-pure : ∀ {A B} p q a b → (step p >> pure {A} a) & (step q >> pure {B} b) ≡ step (p ⊗ q) >> pure (a , b)

  step-pure-&-pure : ∀ {A B} p a b → (step p >> pure {A} a) & pure {B} b ≡ step (p ⊗ 𝟘) >> pure (a , b)
  step-pure-&-pure p a b = trans (cong ((_ >> _) &_) (sym (step-𝟘->> _))) (step-pure-&-step-pure p 𝟘 a b)

  pure-&-step-pure : ∀ {A B} q a b → pure {A} a & (step q >> pure {B} b) ≡ step (𝟘 ⊗ q) >> pure (a , b)
  pure-&-step-pure q a b = trans (cong (_& (_ >> _)) (sym (step-𝟘->> _))) (step-pure-&-step-pure 𝟘 q a b)

  pure-&-pure : ∀ {A B} a b → pure {A} a & pure {B} b ≡ step (𝟘 ⊗ 𝟘) >> pure (a , b)
  pure-&-pure a b = trans (cong (_& _) (sym (step-𝟘->> _))) (step-pure-&-pure 𝟘 a b)
