{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf.Refinement (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.PhaseDistinction costMonoid
open import Calf.Upper costMonoid
open import Calf.Eq

open import Calf.Types.Bool
open import Calf.Types.Sum

open import Relation.Binary.PropositionalEquality as Eq

ub/circ : ∀ {A e} p {q} →
  ub A e q →
  ub A e (step (meta ℂ) p q)
ub/circ p {q = q₁} (ub/intro {q = q} a h1 h2) =
  ub/intro {q = q} a (λ u → subst (q ≤_) (sym (step/ext (meta ℂ) q₁ p u)) (h1 u)) h2

ub/circ' : ∀ {A e} p {q} →
  ub A e (step (meta ℂ) p q) →
  ub A e q
ub/circ' p {q = q₁} (ub/intro {q = q} a h1 h2) =
  ub/intro {q = q} a (λ u → subst (q ≤_) (step/ext (meta ℂ) q₁ p u) (h1 u)) h2


ub/ret : ∀ {A a} → ub A (ret {A} a) zero
ub/ret {A} {a} = ub/intro a (λ _ → ≤-refl) (ret (eq/intro refl))

ub/step : ∀ {A e} (p q : ℂ) →
  ub A e q →
  ub A (step (F A) p e) (p + q)
ub/step p q (ub/intro {q = q1} a h1 h2) with eq/ref h2
...                                              | refl =
   ub/intro {q = p + q1} a (λ u → +-monoʳ-≤ p (h1 u)) (ret (eq/intro refl))

ub/bind : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (p : ℂ) (q : val A → ℂ) →
  ub A e p →
  ((a : val A) → ub B (f a) (q a)) →
  ub B (bind {A} (F B) e f)
       (bind {A} (meta ℂ) e (λ a → p + q a))
ub/bind {f = f} p q (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl with h3 a
... | ub/intro {q = q2} b h4 h5 with f a | eq/ref h5
... | _ | refl =
  ub/circ q1 (ub/intro b (λ u → +-mono-≤ (h1 u) (h4 u)) (ret (eq/intro refl)))

ub/bind/const : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (p q : ℂ) →
  ub A e p →
  ((a : val A) → ub B (f a) q) →
  ub B (bind {A} (F B) e f) (p + q)
ub/bind/const {e = e} {f = f} p q (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl = ub/circ' q1 (ub/bind {e = e} p (λ _ → q) (ub/intro {q = q1} a h1 h2) h3)

ub/bool : ∀ {A : tp pos} {e0 e1} {p : val bool → cmp cost} →
  (b : val bool) →
  ub A e0 (p false) →
  ub A e1 (p true ) →
  ub A (if b then e1 else e0) (p b)
ub/bool false h0 h1 = h0
ub/bool true  h0 h1 = h1

ub/sum/case/const/const : ∀ A B (C : val (sum A B) → tp pos) →
  (s : val (sum A B)) →
  (e0 : (a : val A) → cmp (F (C (inj₁ a)))) →
  (e1 : (b : val B) → cmp (F (C (inj₂ b)))) →
  (p : ℂ) →
  ((a : val A) → ub (C (inj₁ a)) (e0 a) p) →
  ((b : val B) → ub (C (inj₂ b)) (e1 b) p) →
  ub (C s) (sum/case A B (λ s → F (C s)) s e0 e1) p
ub/sum/case/const/const A B C s e0 e1 p h1 h2 = sum/case A B
  (λ s → meta (ub (C s) (sum/case A B (λ s₁ → F (C s₁)) s e0 e1) p)) s h1 h2
