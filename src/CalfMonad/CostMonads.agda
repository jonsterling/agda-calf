{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.CostMonads ℓ ℓ′ where

open Agda.Primitive
open import Data.Product               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (refl;sym; trans; cong; cong₂)

open import CalfMonad.CostMonad ℓ ℓ′ (ℓ ⊔ ℓ′)
open import CalfMonad.CostMonoid ℓ

costMonad : (costMonoid : CostMonoid) → CostMonad costMonoid
costMonad costMonoid = record
  { monad = record
    { M = λ A → ℂ × A
    ; pure = λ a → 𝟘 , a
    ; _>>=_ = λ (p , a) f → let (q , b) = f a in p ⊕ q , b
    ; pure->>= = λ a f → let (p , b) = f a in cong (_, b) (⊕-identityˡ p)
    ; >>=-pure = λ (p , a) → cong (_, a) (⊕-identityʳ p)
    ; >>=->>= = λ (p , a) f g → let (q , b) = f a; (r , c) = g b in cong (_, c) (⊕-assoc p q r)
    }
  ; step = λ p → p , tt
  ; step-𝟘 = refl
  ; step-⊕ = λ p q → refl
  }
  where
    open CostMonoid costMonoid

parCostMonad : (parCostMonoid : ParCostMonoid) → ParCostMonad parCostMonoid
parCostMonad parCostMonoid = record
  { costMonad = costMonad costMonoid
  ; _&_ = λ (p , a) (q , b) → p ⊗ q , a , b
  ; step-pure-&-step-pure = λ p q a b → cong (_, a , b) (trans (cong₂ _⊗_ (⊕-identityʳ p) (⊕-identityʳ q)) (sym (⊕-identityʳ (p ⊗ q))))
  }
  where
    open ParCostMonoid parCostMonoid
