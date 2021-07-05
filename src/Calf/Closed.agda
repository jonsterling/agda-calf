{-# OPTIONS --prop --rewriting #-}

-- This file adds the phase distinction for extension.

open import Calf.CostMonoid

module Calf.Closed (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction costMonoid

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
open import Data.Product
open import Data.Product.Properties
open import Function.Bundles
open import Axiom.UniquenessOfIdentityProofs.WithK

postulate
  ● : tp pos → tp pos
  η : ∀ {A} → val A → val (● A)
  * : ∀ {A} → ext → val (● A)
  η≡* : ∀ {A} (a : val A) u → η {A} a ≡ * u
  ind/● : ∀ {A} (a : val (● A)) (X : val (● A) → tp neg)
    (x0 : (a : val A) → cmp (X (η a))) →
    (x1 : (u : ext) → cmp (X (* u))) →
    ((a : val A) → (u : ext) → P.subst (λ a → cmp (X a)) (η≡* a u) (x0 a) ≡ x1 u ) →
    cmp (X a)

unique : ∀ {A} → (a : val (● A)) → (u : ext) → a ≡ * u
unique {A} a u = ind/● {A} a (λ a → meta (a ≡ * u))
  (λ a → η≡* a u)
  (λ u → refl)
  (λ a u → uip _ _)

noninterference : ∀ {A B} (f : val (● A) → val (◯⁺ B)) →
  Σ (val (● A) → val (◯⁺ B)) λ f' → f ≡ f'
noninterference f =
  (λ a u → f (* u) u) , funext (λ a → funext/Ω (λ u →
    P.cong (λ a → f a u) (unique a u)))

optimization : ∀ {C B : tp pos} {A : val C → tp pos}
  (f : val (Σ++ C λ c → ● (A c)) → val (◯⁺ B)) →
  Σ (val C → val (◯⁺ B)) λ f' → ∀ c a → f (c , a) ≡ f' c
optimization f = (λ c u → f (c , * u) u) ,
  λ c a → funext/Ω (λ u → P.cong (λ a → f a u)
    (Inverse.f Σ-≡,≡↔≡ (refl , unique _ u)))