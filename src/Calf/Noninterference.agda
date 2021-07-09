{-# OPTIONS --prop --without-K --rewriting #-}

-- Theorems about noninterference.

open import Calf.CostMonoid

module Calf.Noninterference (costMonoid : CostMonoid) where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction
open import Calf.Types.Eq

open import Data.Product
open import Relation.Binary.PropositionalEquality as P

oblivious : ∀ {A B} (f : cmp (F A) → val (◯⁺ B)) →
      ∀ c e → f (step (F A) c e) ≡ f e
oblivious {A} {B} f c e = funext/Ω (λ u →
  begin
  f (step (F A) c e) u ≡⟨ cong (λ e → f e u) (step/ext (F A) e c u) ⟩
  f e u
  ∎
  )
  where open ≡-Reasoning

unique : ∀ {A} → (a : val (● A)) → (u : ext) → a ≡ ∗ u
unique {A} a u =
  eq/ref
  (●/ind {A} a (λ a → F (eq (● A) a (∗ u)))
  (λ a → ret (eq/intro (η≡∗ a u)))
  (λ u → ret (eq/intro refl))
  (λ a u → eq/uni _ _ u))

constant : ∀ {A B} (f : val (● A) → val (◯⁺ B)) →
  Σ (val (◯⁺ B)) λ b → f ≡ λ _ → b
constant f =
  (λ u → f (∗ u) u) , funext (λ a → funext/Ω (λ u →
    P.cong (λ a → f a u) (unique a u)))

optimization : ∀ {C B : tp pos} {A : val C → tp pos}
  (f : val (Σ++ C λ c → ● (A c)) → val (◯⁺ B)) →
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
    P.cong-app h a
