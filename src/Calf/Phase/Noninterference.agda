{-# OPTIONS --rewriting #-}

-- Theorems about noninterference.

open import Algebra.Cost

module Calf.Phase.Noninterference where

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Phase.Core
open import Calf.Phase.Open
open import Calf.Phase.Closed
open import Calf.Data.Equality

open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; subst; cong; module ≡-Reasoning)

open import Function


unique : (a : val (● A)) (u : ext) → a ≡ ∗ u
unique {A} a u =
  ●/ind a
    (λ a → val (a ≡⁺[ ● A ] ∗ u))
    (λ a → η≡∗ a u)
    (λ u → refl)
    (λ a u → η≡∗/uni (subst (λ a₂ → a₂ ≡ ∗ u) (η≡∗ a u) (η≡∗ a u)) refl u)

●/map : (val A → val B) → val (● A) → val (● B)
●/map {A} {B} f ●a =
  ●/ind ●a
    (const (val (● B)))
    (η ∘ f)
    ∗
    (λ a u → unique _ u)

-- lemma : (A : Set) {B : Set} {b b' : B} {h : b ≡ b'} (x : A) → subst (λ _ → A) h x ≡ x
-- lemma A {h = refl} x = refl

fracture : (x : val (● A)) (y : val (◯⁺ A)) → ●/map {A} {◯⁺ A} η◯ x ≡ η y → val A
fracture {A} x y h =
  ●/ind x
    (λ _ → val A)
    id
    y
    (λ a u → {!   !})
    -- (λ a u → trans (lemma (val A) a) {!   !})


constant : (f : val (● A) → val (◯⁺ B)) →
  Σ (val (◯⁺ B)) λ b → f ≡ λ _ → b
constant f =
  (λ u → f (∗ u) u) , funext (λ a → funext/Ω (λ u →
    cong (λ a → f a u) (unique a u)))

optimization : {A : val C → tp⁺}
  (f : val (Σ⁺ C λ c → ● (A c)) → val (◯⁺ B)) →
  Σ (val C → val (◯⁺ B)) λ f' → ∀ c a → f (c , a) ≡ f' c
optimization {C} {B} {A} f =
  (λ c →
    let g : val (● (A c)) → val (◯⁺ B)
        g a = f (c , a) in
    let (b , h) = constant {A c} {B} g in
    b) ,
    λ c a →
    let g : val (● (A c)) → val (◯⁺ B)
        g a = f (c , a) in
    let (b , h) = constant {A c} {B} g in
    Eq.cong-app h a

module _ (costMonoid : CostMonoid) where
  open import Calf.Step costMonoid

  oblivious : (f : cmp (F A) → val (◯⁺ B)) →
        ∀ c e → f (step (F A) c e) ≡ f e
  oblivious {A} {B} f c e = funext/Ω λ u →
    begin
      f (step (F A) c e) u
    ≡⟨ cong (λ e → f e u) (step/ext (F A) e c u) ⟩
      f e u
    ∎
    where open ≡-Reasoning
