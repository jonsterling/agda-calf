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
    pure _                    ≡˘⟨ pure->>= _ _ ⟩
    (pure _ >>= λ _ → pure _) ∎

  module _ (parCostMonoid : ParCostMonoid ℂ) where
    parCostMonad : ParCostMonad costMonad parCostMonoid
    parCostMonad ._&_ x y = x >>= λ a → y >>= λ b → pure (a , b)
    parCostMonad .step-pure-&-step-pure p q a b = begin
      ((pure _ >>= λ _ → pure a) >>= λ a → (pure _ >>= λ _ → pure b) >>= λ b → pure (a , b)) ≡⟨ >>=->>= _ _ _ ⟩
      (pure _ >>= λ _ → pure a >>= λ a → (pure _ >>= λ _ → pure b) >>= λ b → pure (a , b))   ≡⟨ pure->>= _ _ ⟩
      (pure a >>= λ a → (pure _ >>= λ _ → pure b) >>= λ b → pure (a , b))                    ≡⟨ pure->>= a _ ⟩
      ((pure _ >>= λ _ → pure b) >>= λ b → pure (a , b))                                     ≡⟨ >>=->>= _ _ _ ⟩
      (pure _ >>= λ _ → pure b >>= λ b → pure (a , b))                                       ≡⟨ pure->>= _ _ ⟩
      (pure b >>= λ b → pure (a , b))                                                        ≡⟨ pure->>= b _ ⟩
      pure (a , b)                                                                           ≡˘⟨ pure->>= _ _ ⟩
      (pure _ >>= λ _ → pure (a , b))                                                        ∎

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
    (pure (𝟘 , a) >>= λ (𝟘′ , a) → f a >>= λ (p , b) → pure (𝟘′ ⊕ p , b)) ≡⟨ pure->>= (𝟘 , a) _ ⟩
    (f a >>= λ (p , b) → pure (𝟘 ⊕ p , b))                                ≡⟨ >>=-cong (f a) (λ (p , b) → cong (λ p → pure (p , b)) (⊕-identityˡ p)) ⟩
    f a >>= pure                                                          ≡⟨ >>=-pure (f a) ⟩
    f a                                                                   ∎
  monad .Monad.>>=-pure x = begin
    (x >>= λ (p , a) → pure (𝟘 , a) >>= λ (𝟘′ , a) → pure (p ⊕ 𝟘′ , a)) ≡⟨ >>=-cong x (λ (p , a) → pure->>= (𝟘 , a) _) ⟩
    (x >>= λ (p , a) → pure (p ⊕ 𝟘 , a))                                ≡⟨ >>=-cong x (λ (p , a) → cong (λ p → pure (p , a)) (⊕-identityʳ p)) ⟩
    x >>= pure                                                          ≡⟨ >>=-pure x ⟩
    x ∎
  monad .Monad.>>=->>= x f g = begin
    ((x >>= λ (p , a) → f a >>= λ (q , b) → pure (p ⊕ q , b)) >>= λ (pq , b) → g b >>= λ (r , c) → pure (pq ⊕ r , c)) ≡⟨ >>=->>= x _ _ ⟩
    (x >>= λ (p , a) → (f a >>= λ (q , b) → pure (p ⊕ q , b)) >>= λ (pq , b) → g b >>= λ (r , c) → pure (pq ⊕ r , c)) ≡⟨ >>=-cong x (λ (p , a) → >>=->>= (f a) _ _) ⟩
    (x >>= λ (p , a) → f a >>= λ (q , b) → pure (p ⊕ q , b) >>= λ (pq , b) → g b >>= λ (r , c) → pure (pq ⊕ r , c))   ≡⟨ >>=-cong x (λ (p , a) → >>=-cong (f a) λ (q , b) → pure->>= (p ⊕ q , b) _) ⟩
    (x >>= λ (p , a) → f a >>= λ (q , b) → g b >>= λ (r , c) → pure ((p ⊕ q) ⊕ r , c))                                ≡⟨ >>=-cong x (λ (p , a) → >>=-cong (f a) λ (q , b) → >>=-cong (g b) λ (r , c) → cong (λ pqr → pure (pqr , c)) (⊕-assoc p q r)) ⟩
    (x >>= λ (p , a) → f a >>= λ (q , b) → g b >>= λ (r , c) → pure (p ⊕ (q ⊕ r) , c))                                ≡˘⟨ >>=-cong x (λ (p , a) → >>=-cong (f a) λ (q , b) → >>=-cong (g b) λ (r , c) → pure->>= (q ⊕ r , c) _) ⟩
    (x >>= λ (p , a) → f a >>= λ (q , b) → g b >>= λ (r , c) → pure (q ⊕ r , c) >>= λ (qr , c) → pure (p ⊕ qr , c))   ≡˘⟨ >>=-cong x (λ (p , a) → >>=-cong (f a) λ (q , b) → >>=->>= (g b) _ _) ⟩
    (x >>= λ (p , a) → f a >>= λ (q , b) → (g b >>= λ (r , c) → pure (q ⊕ r , c)) >>= λ (qr , c) → pure (p ⊕ qr , c)) ≡˘⟨ >>=-cong x (λ (p , a) → >>=->>= (f a) _ _) ⟩
    (x >>= λ (p , a) → (f a >>= λ (q , b) → g b >>= λ (r , c) → pure (q ⊕ r , c)) >>= λ (qr , c) → pure (p ⊕ qr , c)) ∎

  monadLift : MonadLift M′ M
  monadLift .lift = _>>=_

  costMonad : CostMonad monad costMonoid
  costMonad .step p = pure (p , _)
  costMonad .step-𝟘 = begin
    pure (𝟘 , _) ∎
  costMonad .step-⊕ p q = begin
    pure (p ⊕ q , _)                                                             ≡˘⟨ pure->>= (q , _) _ ⟩
    (pure (q , _) >>= λ (q , _) → pure (p ⊕ q , _))                              ≡˘⟨ pure->>= (p , _) _ ⟩
    (pure (p , _) >>= λ (p , _) → pure (q , _) >>= λ (q , _) → pure (p ⊕ q , _)) ∎

  module _ (parCostMonoid : ParCostMonoid ℂ) where
    open ParCostMonoid parCostMonoid

    parCostMonad : ParCostMonad costMonad parCostMonoid
    parCostMonad ._&_ x y = x >>= λ (p , a) → y >>= λ (q , b) → pure (p ⊗ q , a , b)
    parCostMonad .step-pure-&-step-pure p q a b = begin
      ((pure (p , _) >>= λ (p , _) → pure (𝟘 , a) >>= λ (𝟘′ , a) → pure (p ⊕ 𝟘′ , a)) >>= λ (p , a) → (pure (q , _) >>= λ (q , _) → pure (𝟘 , b) >>= λ (𝟘′ , b) → pure (q ⊕ 𝟘′ , b)) >>= λ (q , b) → pure (p ⊗ q , a , b)) ≡⟨ cong (_>>= λ _ → (_ >>= λ _ → _ >>= _) >>= _) (pure->>= (p , _) _) ⟩
      ((pure (𝟘 , a) >>= λ (𝟘′ , a) → pure (p ⊕ 𝟘′ , a)) >>= λ (p , a) → (pure (q , _) >>= λ (q , _) → pure (𝟘 , b) >>= λ (𝟘′ , b) → pure (q ⊕ 𝟘′ , b)) >>= λ (q , b) → pure (p ⊗ q , a , b))                              ≡⟨ cong (_>>= λ _ → (_ >>= λ _ → _ >>= _) >>= _) (pure->>= (𝟘 , a) _) ⟩
      (pure (p ⊕ 𝟘 , a) >>= λ (p , a) → (pure (q , _) >>= λ (q , _) → pure (𝟘 , b) >>= λ (𝟘′ , b) → pure (q ⊕ 𝟘′ , b)) >>= λ (q , b) → pure (p ⊗ q , a , b))                                                               ≡⟨ pure->>= (p ⊕ 𝟘 , a) _ ⟩
      ((pure (q , _) >>= λ (q , _) → pure (𝟘 , b) >>= λ (𝟘′ , b) → pure (q ⊕ 𝟘′ , b)) >>= λ (q , b) → pure ((p ⊕ 𝟘) ⊗ q , a , b))                                                                                          ≡⟨ cong (_>>= _) (pure->>= (q , _) _) ⟩
      ((pure (𝟘 , b) >>= λ (𝟘′ , b) → pure (q ⊕ 𝟘′ , b)) >>= λ (q , b) → pure ((p ⊕ 𝟘) ⊗ q , a , b))                                                                                                                       ≡⟨ cong (_>>= _) (pure->>= (𝟘 , b) _) ⟩
      ((pure (q ⊕ 𝟘 , b)) >>= λ (q , b) → pure ((p ⊕ 𝟘) ⊗ q , a , b))                                                                                                                                                      ≡⟨ pure->>= (q ⊕ 𝟘 , b) _ ⟩
      pure ((p ⊕ 𝟘) ⊗ (q ⊕ 𝟘) , a , b)                                                                                                                                                                                     ≡⟨ cong₂ (λ p q → pure (p ⊗ q , a , b)) (⊕-identityʳ p) (⊕-identityʳ q) ⟩
      pure (p ⊗ q , a , b)                                                                                                                                                                                                 ≡˘⟨ cong (λ pq → pure (pq , a , b)) (⊕-identityʳ (p ⊗ q)) ⟩
      pure ((p ⊗ q) ⊕ 𝟘 , a , b)                                                                                                                                                                                           ≡˘⟨ pure->>= (𝟘 , a , b) _ ⟩
      (pure (𝟘 , a , b) >>= λ (𝟘′ , a,b) → pure ((p ⊗ q) ⊕ 𝟘′ , a,b))                                                                                                                                                      ≡˘⟨ pure->>= (p ⊗ q , _) _ ⟩
      (pure (p ⊗ q , _) >>= λ (pq , _) → pure (𝟘 , a , b) >>= λ (𝟘′ , a,b) → pure (pq ⊕ 𝟘′ , a,b))                                                                                                                         ∎

module WriterMonad ℓ {ℓ′} {ℂ : Set ℓ′} (costMonoid : CostMonoid ℂ) = WriterMonadT ℓ (IdentityMonad.monad _) costMonoid
