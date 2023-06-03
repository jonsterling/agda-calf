{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Monads where

open import Data.List.Base       using (List; [_]; concat; map)
open import Data.List.Properties using (++-identityʳ; concat-[-]; concat-concat; concat-map; map-compose; map-cong)
open import Function.Base        using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; cong; refl)

open import CalfMonad.Monad

open Monad
open ≡-Reasoning

module IdentityMonad ℓ where
  M : Set ℓ → Set ℓ
  M A = A

  monad : Monad M
  monad .pure a = a
  monad ._>>=_ a f = f a
  monad .>>=-cong a eq = eq a
  monad .pure->>= a f = refl
  monad .>>=-pure a = refl
  monad .>>=->>= a f g = refl

module ListMonad ℓ where
  M : Set ℓ → Set ℓ
  M = List

  monad : Monad M
  monad .pure = [_]
  monad ._>>=_ l f = concat (map f l)
  monad .>>=-cong l eq = cong concat (map-cong eq l)
  monad .pure->>= a f = ++-identityʳ (f a)
  monad .>>=-pure = concat-[-]
  monad .>>=->>= l f g = begin
    concat (map g (concat (map f l)))       ≡˘⟨ cong concat (concat-map (map f l)) ⟩
    concat (concat (map (map g) (map f l))) ≡˘⟨ cong (concat ∘ concat) (map-compose l) ⟩
    concat (concat (map (map g ∘ f) l))     ≡˘⟨ concat-concat (map (map g ∘ f) l) ⟩
    concat (map concat (map (map g ∘ f) l)) ≡˘⟨ cong concat (map-compose l) ⟩
    concat (map (concat ∘ map g ∘ f) l)     ∎
