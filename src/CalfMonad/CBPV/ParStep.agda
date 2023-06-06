{-# OPTIONS --cubical-compatible --lossy-unification --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad

module CalfMonad.CBPV.ParStep {ℓ ℓ′} {M : Set ℓ → Set ℓ} {ℂ : Set ℓ′} {monad : Monad M} {costMonoid : CostMonoid ℂ} {costMonad : CostMonad monad costMonoid} {parCostMonoid : ParCostMonoid ℂ} (parCostMonad : ParCostMonad costMonad parCostMonoid) where

open CostMonoid costMonoid
open ParCostMonoid parCostMonoid

open import Axiom.Extensionality.Propositional         using (Extensionality)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong)

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Step costMonad
open import CalfMonad.CBPV.Types.Sigma monad

open ≡-Reasoning

infix 5 _&_

_&_ : ∀ {A B} → cmp (F A) → cmp (F B) → cmp (F (A ×′ B))
_&_ = ParCostMonad._&_ parCostMonad

step-ret-&-step-ret : ∀ {A B} p q a b → bind (step p) (λ _ → ret {A} a) & bind (step q) (λ _ → ret {B} b) ≡ bind (step (p ⊗ q)) λ _ → ret (a , b)
step-ret-&-step-ret = ParCostMonad.step-pure-&-step-pure parCostMonad

module _ (ext : Extensionality ℓ ℓ) where
  step-ret-&-ret : ∀ {A B} p a b → bind (step p) (λ _ → ret {A} a) & ret {B} b ≡ bind (step (p ⊗ 𝟘)) λ _ → ret (a , b)
  step-ret-&-ret p a b = begin
    bind (step p) (λ _ → ret a) & ret b                       ≡˘⟨ cong (bind _ (λ _ → ret a) &_) (≈⇒≡ ext (ret-bind _ _)) ⟩
    bind (step p) (λ _ → ret a) & bind (ret _) (λ _ → ret b)  ≡˘⟨ cong (λ e → bind _ _ & bind e _) step-𝟘 ⟩
    bind (step p) (λ _ → ret a) & bind (step 𝟘) (λ _ → ret b) ≡⟨ step-ret-&-step-ret p 𝟘 a b ⟩
    bind (step (p ⊗ 𝟘)) (λ _ → ret (a , b))                   ∎

  ret-&-step-ret : ∀ {A B} q a b → ret {A} a & bind (step q) (λ _ → ret {B} b) ≡ bind (step (𝟘 ⊗ q)) λ _ → ret (a , b)
  ret-&-step-ret q a b = begin
    ret a & bind (step q) (λ _ → ret b)                       ≡˘⟨ cong (_& bind _ (λ _ → ret b)) (≈⇒≡ ext (ret-bind _ _)) ⟩
    bind (ret _) (λ _ → ret a) & bind (step q) (λ _ → ret b)  ≡˘⟨ cong (λ e → bind e _ & bind _ _) step-𝟘 ⟩
    bind (step 𝟘) (λ _ → ret a) & bind (step q) (λ _ → ret b) ≡⟨ step-ret-&-step-ret 𝟘 q a b ⟩
    bind (step (𝟘 ⊗ q)) (λ _ → ret (a , b))                   ∎

  ret-&-ret : ∀ {A B} a b → ret {A} a & ret {B} b ≡ bind (step (𝟘 ⊗ 𝟘)) λ _ → ret (a , b)
  ret-&-ret a b = begin
    ret a & ret b                           ≡˘⟨ cong (_& ret b) (≈⇒≡ ext (ret-bind _ _)) ⟩
    bind (ret _) (λ _ → ret a) & ret b      ≡˘⟨ cong (λ e → bind e _ & _) step-𝟘 ⟩
    bind (step 𝟘) (λ _ → ret a) & ret b     ≡⟨ step-ret-&-ret 𝟘 a b ⟩
    bind (step (𝟘 ⊗ 𝟘)) (λ _ → ret (a , b)) ∎
