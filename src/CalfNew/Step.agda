{-# OPTIONS --cubical-compatible --lossy-unification --rewriting #-}

open import CalfNew.CostMonoid

module CalfNew.Step (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import CalfNew.Prelude
import CalfNew.Metalanguage as Metalanguage

module Imp where
  open Metalanguage.Imp

  postulate
    M/step : ∀ {A} → ℂ → M A → M A

    M/bind-step : ∀ {A B} p e f → M/bind {A} {B} (M/step p e) f ≡ M/step p (M/bind e f)

    M/step-𝟘 : ∀ {A} e → M/step {A} 𝟘 e ≡ e
    M/step-step : ∀ {A} p q e → M/step {A} p (M/step q e) ≡ M/step (p ⊕ q) e

  step : ∀ X → ℂ → cmp X → cmp X
  step (F A) = M/step
  step (Π A X) p f a = step (X a) p (f a)

  bind-step : ∀ {A} X p e f → bind X (step (F A) p e) f ≡ step X p (bind X e f)
  bind-step (F B) = M/bind-step
  bind-step (Π B X) p e f = funext λ b → bind-step (X b) p e λ a → f a b

  step-𝟘 : ∀ X e → step X 𝟘 e ≡ e
  step-𝟘 (F A) = M/step-𝟘
  step-𝟘 (Π A X) e = funext λ a → step-𝟘 (X a) (e a)

  step-step : ∀ X p q e → step X p (step X q e) ≡ step X (p ⊕ q) e
  step-step (F A) = M/step-step
  step-step (Π A X) p q e = funext λ a → step-step (X a) p q (e a)

open Metalanguage

cost : tp+
cost = meta ℂ

opaque
  unfolding cmp

  step : ∀ X → val cost → cmp X → cmp X
  step = Imp.step

  private
    step-Π : ∀ {A X p f a} → step (Π A X) p f a ≡ step (X a) p (f a)
    step-Π = refl
    {-# REWRITE step-Π #-}

    bind-step : ∀ {A} X p e f → bind X (step (F A) p e) f ≡ step X p (bind X e f)
    bind-step = Imp.bind-step
    {-# REWRITE bind-step #-}

    step-𝟘 : ∀ X e → step X 𝟘 e ≡ e
    step-𝟘 = Imp.step-𝟘
    {-# REWRITE step-𝟘 #-}

    step-step : ∀ X p q e → step X p (step X q e) ≡ step X (p ⊕ q) e
    step-step = Imp.step-step
    {-# REWRITE step-step #-}
