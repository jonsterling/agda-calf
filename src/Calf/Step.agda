{-# OPTIONS --prop --without-K --rewriting #-}

-- Step effect.

open import Calf.CostMonoid

module Calf.Step (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Relation.Binary.PropositionalEquality

cost : tp neg
cost = meta ℂ

postulate
  step' : ∀ (B : tp neg) → cmp cost → cmp B → cmp B
  step'/id : ∀ {B : tp neg} {e : cmp B} →
    step' B zero e ≡ e
  {-# REWRITE step'/id #-}
  step'/concat : ∀ {B e p q} →
    step' B p (step' B q e) ≡ step' B (p + q) e
  {-# REWRITE step'/concat #-}

  U_step' : ∀ {A} {X : val A → tp neg} {e n} → U (tbind {A} (step' (F A) n e) X) ≡ U (tbind {A} e X)
  {-# REWRITE U_step' #-}

  Π/step' : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} {n} → step' (Π A X) n f ≡ λ x → step' (X x) n (f x)
  {-# REWRITE Π/step' #-}

  bind/step' : ∀ {A} {X} {e f n} → bind {A} X (step' (F A) n e) f ≡ step' X n (bind {A} X e f)
  dbind/step' : ∀ {A} {X : val A → tp neg} {e f n} → dbind {A} X (step' (F A) n e) f ≡ step' (tbind {A} e X) n (dbind {A} X e f)
  {-# REWRITE bind/step' dbind/step' #-}

  meta/step' : ∀ {A n} → (e : cmp (meta A)) → step' (meta A) n e ≡ e
  {-# REWRITE meta/step' #-}
