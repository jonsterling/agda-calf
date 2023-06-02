{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonads where

open Agda.Primitive
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (refl; sym; trans; cong; cong₂)

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad

module WriterMonad {ℓ ℓ′} {ℂ : Set ℓ′} (costMonoid : CostMonoid ℂ) where
  open CostMonoid costMonoid
  open Monad
  open CostMonad

  M : Set ℓ → Set (ℓ ⊔ ℓ′)
  M = ℂ ×_

  monad : Monad M
  monad .pure = 𝟘 ,_
  monad ._>>=_ (p , a) f = let (q , b) = f a in p ⊕ q , b
  monad .pure->>= a f = let (p , b) = f a in cong (_, b) (⊕-identityˡ p)
  monad .>>=-pure (p , a) = cong (_, a) (⊕-identityʳ p)
  monad .>>=->>= (p , a) f g = let (q , b) = f a; (r , c) = g b in cong (_, c) (⊕-assoc p q r)

  costMonad : CostMonad monad costMonoid
  costMonad .step = _, tt
  costMonad .step-𝟘 = refl
  costMonad .step-⊕ p q = refl

  module _ (parCostMonoid : ParCostMonoid ℂ) where
    open ParCostMonoid parCostMonoid
    open ParCostMonad

    parCostMonad : ParCostMonad costMonad parCostMonoid
    parCostMonad ._&_ (p , a) (q , b) = p ⊗ q , a , b
    parCostMonad .step-pure-&-step-pure p q a b = cong (_, a , b) (trans (cong₂ _⊗_ (⊕-identityʳ p) (⊕-identityʳ q)) (sym (⊕-identityʳ (p ⊗ q))))
