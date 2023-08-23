{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonad where

open Agda.Primitive
open import Data.Product                               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base                 using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong)

open import CalfMonad.CostMonoid
open import CalfMonad.Monad

open ≡-Reasoning

record CostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} (monad : Monad M) (costMonoid : CostMonoid ℂ) : Set (ℓ′ ⊔ ℓ″) where
  open Monad monad
  open CostMonoid costMonoid

  field
    step : ℂ → M ⊤

    step-𝟘 : step 𝟘 ≡ pure _
    step-⊕ : ∀ p q → step (p ⊕ q) ≡ step p >> step q

  step-𝟘->> : ∀ {A} (x : M A) → step 𝟘 >> x ≡ x
  step-𝟘->> x = begin
    step 𝟘 >> x ≡⟨ cong (_>> _) step-𝟘 ⟩
    pure _ >> x ≡⟨ pure->>= _ _ ⟩
    x           ∎

  ext : Set (ℓ′ ⊔ ℓ″)
  ext = ∀ p → step p ≡ pure _

  ext/step->> : ext → ∀ {A} p (x : M A) → step p >> x ≡ x
  ext/step->> u p x = begin
    step p >> x ≡⟨ cong (_>> _) (u p) ⟩
    pure _ >> x ≡⟨ pure->>= _ _ ⟩
    x           ∎

record ParCostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} {monad : Monad M} {costMonoid : CostMonoid ℂ} (costMonad : CostMonad monad costMonoid) (parCostMonoid : ParCostMonoid ℂ) : Set (lsuc ℓ ⊔ ℓ′ ⊔ ℓ″) where
  infix 5 _&_

  open Monad monad
  open CostMonoid costMonoid
  open CostMonad costMonad
  open ParCostMonoid parCostMonoid

  field
    _&_ : ∀ {A B} → M A → M B → M (A × B)

    >>=-pure-&->>=-pure : ∀ {A B C D} x y (f : A → C) (g : B → D) → (x >>= λ a → pure (f a)) & (y >>= λ b → pure (g b)) ≡ (x & y) >>= λ (a , b) → pure (f a , g b)
    step-&-step : ∀ p q → (step p & step q) ≡ step (p ⊗ q) >> pure _

  step-pure-&-step-pure : ∀ {A B} p q a b → (step p >> pure {A} a) & (step q >> pure {B} b) ≡ step (p ⊗ q) >> pure (a , b)
  step-pure-&-step-pure p q a b = begin
    (step p >> pure a) & (step q >> pure b)  ≡⟨ >>=-pure-&->>=-pure _ _ _ _ ⟩
    (step p & step q) >> pure (a , b)        ≡⟨ cong (_>> _) (step-&-step p q) ⟩
    (step (p ⊗ q) >> pure _) >> pure (a , b) ≡⟨ >>=->>= _ _ _ ⟩
    step (p ⊗ q) >> (pure _ >> pure (a , b)) ≡⟨ cong (_ >>_) (pure->>= _ _) ⟩
    step (p ⊗ q) >> pure (a , b)             ∎
