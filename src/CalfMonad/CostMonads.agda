{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonads where

open Agda.Primitive
open import Data.Product                               using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; cong₂)

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad
open import CalfMonad.Monads

open MonadLift
open CostMonad
open ParCostMonad
open ≡-Reasoning

module ZeroCostMonad {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} (monad : Monad M) (costMonoid : CostMonoid ℂ) where
  open Monad monad

  costMonad : CostMonad monad costMonoid
  costMonad .step p = pure _
  costMonad .step-𝟘 = begin
    pure _ ∎
  costMonad .step-⊕ p q = begin
    pure _           ≡˘⟨ pure->>= _ _ ⟩
    pure _ >> pure _ ∎

  module _ (parCostMonoid : ParCostMonoid ℂ) where
    parCostMonad : ParCostMonad costMonad parCostMonoid
    parCostMonad ._&_ x y = x >>= λ a → y >>= λ b → pure (a , b)
    parCostMonad .>>=-pure-&->>=-pure x y f g = begin
      (x >>= λ a → pure (f a)) >>= (λ c → (y >>= λ b → pure (g b)) >>= λ d → pure (c , d)) ≡⟨ >>=->>= x _ _ ⟩
      x >>= (λ a → pure (f a) >>= λ c → (y >>= λ b → pure (g b)) >>= λ d → pure (c , d))   ≡⟨ >>=-cong x (λ a → pure->>= _ _) ⟩
      x >>= (λ a → (y >>= λ b → pure (g b)) >>= λ d → pure (f a , d))                      ≡⟨ >>=-cong x (λ a → >>=->>= y _ _) ⟩
      x >>= (λ a → y >>= λ b → pure (g b) >>= λ d → pure (f a , d))                        ≡⟨ >>=-cong x (λ a → >>=-cong y λ b → pure->>= _ _) ⟩
      x >>= (λ a → y >>= λ b → pure (f a , g b))                                           ≡˘⟨ >>=-cong x (λ a → >>=-cong y λ b → pure->>= _ _) ⟩
      x >>= (λ a → y >>= λ b → pure (a , b) >>= λ (a , b) → pure (f a , g b))              ≡˘⟨ >>=-cong x (λ a → >>=->>= y _ _) ⟩
      x >>= (λ a → (y >>= λ b → pure (a , b)) >>= λ (a , b) → pure (f a , g b))            ≡˘⟨ >>=->>= x _ _ ⟩
      (x >>= λ a → y >>= λ b → pure (a , b)) >>= (λ (a , b) → pure (f a , g b))            ∎
    parCostMonad .step-&-step p q = begin
      pure _ >> (pure _ >> pure _) ≡⟨ pure->>= _ _ ⟩
      pure _ >> pure _             ∎

module WriterMonadT ℓ {ℓ′ ℓ″} {M = M′ : Set (ℓ ⊔ ℓ″) → Set ℓ′} {ℂ : Set ℓ″} (monad′ : Monad M′) (costMonoid : CostMonoid ℂ) where
  open Monad monad′
  open CostMonoid costMonoid

  M : Set ℓ → Set ℓ′
  M A = M′ (ℂ × A)

  monad : Monad M
  monad .Monad.pure a = pure (𝟘 , a)
  monad .Monad._>>=_ x f = x >>= λ (p , a) → f a >>= λ (q , b) → pure (p ⊕ q , b)
  monad .Monad.>>=-cong x eq = >>=-cong x λ (p , a) → cong (_>>= _) (eq a)
  monad .Monad.pure->>= a f = begin
    pure (𝟘 , a) >>= (λ (𝟘′ , a) → f a >>= λ (p , b) → pure (𝟘′ ⊕ p , b)) ≡⟨ pure->>= _ _ ⟩
    f a >>= (λ (p , b) → pure (𝟘 ⊕ p , b))                                ≡⟨ >>=-cong _ (λ pb → cong (λ p → pure (p , _)) (⊕-identityˡ _)) ⟩
    f a >>= pure                                                          ≡⟨ >>=-pure _ ⟩
    f a                                                                   ∎
  monad .Monad.>>=-pure x = begin
    x >>= (λ (p , a) → pure (𝟘 , a) >>= λ (𝟘′ , a) → pure (p ⊕ 𝟘′ , a)) ≡⟨ >>=-cong x (λ pa → pure->>= _ _) ⟩
    x >>= (λ (p , a) → pure (p ⊕ 𝟘 , a))                                ≡⟨ >>=-cong x (λ pa → cong (λ p → pure (p , _)) (⊕-identityʳ _)) ⟩
    x >>= pure                                                          ≡⟨ >>=-pure x ⟩
    x ∎
  monad .Monad.>>=->>= x f g = begin
    (x >>= λ (p , a) → f a >>= λ (q , b) → pure (p ⊕ q , b)) >>= (λ (pq , b) → g b >>= λ (r , c) → pure (pq ⊕ r , c)) ≡⟨ >>=->>= x _ _ ⟩
    x >>= (λ (p , a) → (f a >>= λ (q , b) → pure (p ⊕ q , b)) >>= λ (pq , b) → g b >>= λ (r , c) → pure (pq ⊕ r , c)) ≡⟨ >>=-cong x (λ pa → >>=->>= _ _ _) ⟩
    x >>= (λ (p , a) → f a >>= λ (q , b) → pure (p ⊕ q , b) >>= λ (pq , b) → g b >>= λ (r , c) → pure (pq ⊕ r , c))   ≡⟨ >>=-cong x (λ pa → >>=-cong _ λ qb → pure->>= _ _) ⟩
    x >>= (λ (p , a) → f a >>= λ (q , b) → g b >>= λ (r , c) → pure ((p ⊕ q) ⊕ r , c))                                ≡⟨ >>=-cong x (λ pa → >>=-cong _ λ qb → >>=-cong _ λ rc → cong (λ pqr → pure (pqr , _)) (⊕-assoc _ _ _)) ⟩
    x >>= (λ (p , a) → f a >>= λ (q , b) → g b >>= λ (r , c) → pure (p ⊕ (q ⊕ r) , c))                                ≡˘⟨ >>=-cong x (λ pa → >>=-cong _ λ qb → >>=-cong _ λ rc → pure->>= _ _) ⟩
    x >>= (λ (p , a) → f a >>= λ (q , b) → g b >>= λ (r , c) → pure (q ⊕ r , c) >>= λ (qr , c) → pure (p ⊕ qr , c))   ≡˘⟨ >>=-cong x (λ pa → >>=-cong _ λ qb → >>=->>= _ _ _) ⟩
    x >>= (λ (p , a) → f a >>= λ (q , b) → (g b >>= λ (r , c) → pure (q ⊕ r , c)) >>= λ (qr , c) → pure (p ⊕ qr , c)) ≡˘⟨ >>=-cong x (λ pa → >>=->>= _ _ _) ⟩
    x >>= (λ (p , a) → (f a >>= λ (q , b) → g b >>= λ (r , c) → pure (q ⊕ r , c)) >>= λ (qr , c) → pure (p ⊕ qr , c)) ∎

  monadLift : MonadLift M′ M
  monadLift .lift = _>>=_

  costMonad : CostMonad monad costMonoid
  costMonad .step p = pure (p , _)
  costMonad .step-𝟘 = begin
    pure (𝟘 , _) ∎
  costMonad .step-⊕ p q = begin
    pure (p ⊕ q , _)                                                             ≡˘⟨ pure->>= _ _ ⟩
    pure (q , _) >>= (λ (q , _) → pure (p ⊕ q , _))                              ≡˘⟨ pure->>= _ _ ⟩
    pure (p , _) >>= (λ (p , _) → pure (q , _) >>= λ (q , _) → pure (p ⊕ q , _)) ∎

  module _ (parCostMonoid : ParCostMonoid ℂ) where
    open ParCostMonoid parCostMonoid

    parCostMonad : ParCostMonad costMonad parCostMonoid
    parCostMonad ._&_ x y = x >>= λ (p , a) → y >>= λ (q , b) → pure (p ⊗ q , a , b)
    parCostMonad .>>=-pure-&->>=-pure x y f g = begin
      (x >>= λ (p , a) → pure (𝟘 , f a) >>= λ (𝟘′ , c) → pure (p ⊕ 𝟘′ , c)) >>= (λ (p , c) → (y >>= λ (q , b) → pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d)) >>= λ (q , d) → pure (p ⊗ q , c , d)) ≡⟨ >>=->>= x _ _ ⟩
      x >>= (λ (p , a) → (pure (𝟘 , f a) >>= λ (𝟘′ , c) → pure (p ⊕ 𝟘′ , c)) >>= λ (p , c) → (y >>= λ (q , b) → pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d)) >>= λ (q , d) → pure (p ⊗ q , c , d)) ≡⟨ >>=-cong x (λ pa → >>=->>= _ _ _) ⟩
      x >>= (λ (p , a) → pure (𝟘 , f a) >>= λ (𝟘′ , c) → pure (p ⊕ 𝟘′ , c) >>= λ (p , c) → (y >>= λ (q , b) → pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d)) >>= λ (q , d) → pure (p ⊗ q , c , d))   ≡⟨ >>=-cong x (λ pa → pure->>= _ _) ⟩
      x >>= (λ (p , a) → pure (p ⊕ 𝟘 , f a) >>= λ (p , c) → (y >>= λ (q , b) → pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d)) >>= λ (q , d) → pure (p ⊗ q , c , d))                                  ≡⟨ >>=-cong x (λ pa → pure->>= _ _) ⟩
      x >>= (λ (p , a) → (y >>= λ (q , b) → pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d)) >>= λ (q , d) → pure ((p ⊕ 𝟘) ⊗ q , f a , d))                                                             ≡⟨ >>=-cong x (λ pa → >>=->>= y _ _) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → (pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d)) >>= λ (q , d) → pure ((p ⊕ 𝟘) ⊗ q , f a , d))                                                             ≡⟨ >>=-cong x (λ pa → >>=-cong y λ qb → >>=->>= _ _ _) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure (𝟘 , g b) >>= λ (𝟘′ , d) → pure (q ⊕ 𝟘′ , d) >>= λ (q , d) → pure ((p ⊕ 𝟘) ⊗ q , f a , d))                                                               ≡⟨ >>=-cong x (λ pa → >>=-cong y λ qb → pure->>= _ _) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure (q ⊕ 𝟘 , g b) >>= λ (q , d) → pure ((p ⊕ 𝟘) ⊗ q , f a , d))                                                                                              ≡⟨ >>=-cong x (λ pa → >>=-cong y λ qb → pure->>= _ _) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure ((p ⊕ 𝟘) ⊗ (q ⊕ 𝟘) , f a , g b))                                                                                                                         ≡⟨ >>=-cong x (λ pa → >>=-cong y λ qb → cong₂ (λ p q → pure (p ⊗ q , _)) (⊕-identityʳ _) (⊕-identityʳ _)) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure (p ⊗ q , f a , g b))                                                                                                                                     ≡˘⟨ >>=-cong x (λ pa → >>=-cong y λ qb → cong (λ pq → pure (pq , _)) (⊕-identityʳ _)) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure ((p ⊗ q) ⊕ 𝟘 , f a , g b))                                                                                                                               ≡˘⟨ >>=-cong x (λ pa → >>=-cong y λ qb → pure->>= _ _) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure (𝟘 , f a , g b) >>= λ (𝟘′ , cd) → pure ((p ⊗ q) ⊕ 𝟘′ , cd))                                                                                              ≡˘⟨ >>=-cong x (λ pa → >>=-cong y λ qb → pure->>= _ _) ⟩
      x >>= (λ (p , a) → y >>= λ (q , b) → pure (p ⊗ q , a , b) >>= λ (pq , a , b) → pure (𝟘 , f a , g b) >>= λ (𝟘′ , cd) → pure (pq ⊕ 𝟘′ , cd))                                                         ≡˘⟨ >>=-cong x (λ pa → >>=->>= y _ _) ⟩
      x >>= (λ (p , a) → (y >>= λ (q , b) → pure (p ⊗ q , a , b)) >>= λ (pq , a , b) → pure (𝟘 , f a , g b) >>= λ (𝟘′ , cd) → pure (pq ⊕ 𝟘′ , cd))                                                       ≡˘⟨ >>=->>= x _ _ ⟩
      (x >>= λ (p , a) → y >>= λ (q , b) → pure (p ⊗ q , a , b)) >>= (λ (pq , a , b) → pure (𝟘 , f a , g b) >>= λ (𝟘′ , cd) → pure (pq ⊕ 𝟘′ , cd))                                                       ∎
    parCostMonad .step-&-step p q = begin
      pure (p , _) >>= (λ (p , _) → pure (q , _) >>= λ (q , _) → pure (p ⊗ q , _))         ≡⟨ pure->>= _ _ ⟩
      pure (q , _) >>= (λ (q , _) → pure (p ⊗ q , _))                                      ≡⟨ pure->>= _ _ ⟩
      pure (p ⊗ q , _)                                                                     ≡˘⟨ cong (λ pq → pure (pq , _)) (⊕-identityʳ _) ⟩
      pure ((p ⊗ q) ⊕ 𝟘 , _)                                                               ≡˘⟨ pure->>= _ _ ⟩
      pure (𝟘 , _) >>= (λ (𝟘′ , _) → pure ((p ⊗ q) ⊕ 𝟘′ , _))                              ≡˘⟨ pure->>= _ _ ⟩
      pure (p ⊗ q , _) >>= (λ (pq , _) → pure (𝟘 , _) >>= λ (𝟘′ , _) → pure (pq ⊕ 𝟘′ , _)) ∎

module WriterMonad ℓ {ℓ′} {ℂ : Set ℓ′} (costMonoid : CostMonoid ℂ) = WriterMonadT ℓ (IdentityMonad.monad _) costMonoid
