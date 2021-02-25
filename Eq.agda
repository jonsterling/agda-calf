{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost

postulate
  eq : (A : tp pos) → val A → val A → tp pos
  eq/intro : ∀ {A v} → val (eq A v v)
  eq/ref : ∀ {A v1 v2} → val (eq A v1 v2) → v1 ≡ v2 
  eq/uni : ∀ {A v1 v2} → (p q : val (eq A v1 v2)) → p ≡ q