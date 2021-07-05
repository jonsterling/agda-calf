{-# OPTIONS --prop --rewriting #-}

-- This file adds the phase distinction for extension.

open import Calf.CostMonoid

module Calf.Closed (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction costMonoid
open import Calf.Eq

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
open import Data.Product
open import Function.Bundles
open import Axiom.UniquenessOfIdentityProofs.WithK

-- This should probably be in Eq.agda
postulate
  eq/uni : ∀ {A v1 v2} → (p q : cmp (F (eq A v1 v2))) →
    (u : ext) → p ≡ q

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
unique {A} a u =
  eq/ref
  (ind/● {A} a (λ a → F (eq (● A) a (* u)))
  (λ a → ret (eq/intro (η≡* a u)))
  (λ u → ret (eq/intro refl))
  (λ a u → eq/uni _ _ u))

noninterference : ∀ {A B} (f : val (● A) → val (◯⁺ B)) →
  Σ (val (◯⁺ B)) λ b → f ≡ λ _ → b
noninterference f =
  (λ u → f (* u) u) , funext (λ a → funext/Ω (λ u →
    P.cong (λ a → f a u) (unique a u)))

optimization : ∀ {C B : tp pos} {A : val C → tp pos}
  (f : val (Σ++ C λ c → ● (A c)) → val (◯⁺ B)) →
  Σ (val C → val (◯⁺ B)) λ f' → ∀ c a → f (c , a) ≡ f' c
optimization {C} {B} {A} f =
  (λ c →
    let g : val (● (A c)) → val (◯⁺ B)
        g a = f (c , a) in
    let (b , h) = noninterference {A c} {B} g in
    b) ,
    λ c a →
    let g : val (● (A c)) → val (◯⁺ B)
        g a = f (c , a) in
    let (b , h) = noninterference {A c} {B} g in
    P.cong-app h a