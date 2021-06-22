{-# OPTIONS --prop --rewriting #-}

open import Calf.CostMonoid

module Calf.Refinement (CostMonoid : CostMonoid) where

open import Calf.Prelude
open import Calf.Metalanguage CostMonoid
open import Calf.PhaseDistinction CostMonoid
open import Calf.Upper CostMonoid
open import Calf.Eq CostMonoid
open import Calf.BoundedFunction CostMonoid

open import Data.Nat as ℕ using (ℕ; suc)
open import Calf.Types.Nat CostMonoid as Nat hiding (zero)
open import Calf.Types.Sum CostMonoid

open import Relation.Binary.PropositionalEquality as P
open import Function using (const)

open CostMonoid CostMonoid

open iso

ub/ret : ∀ {A a} (c : ℂ) → ub A (ret {A} a) c
ub/ret {A} {a} c = ub/intro {q = zero} a z≤c (ret {eq _ _ _} (eq/intro refl))

ub/step : ∀ {A e} (p q : ℂ) →
  ub A e p →
  ub A (step' (F A) q e) (p + q)
ub/step p q (ub/intro {q = q1} a h1 h2) with eq/ref h2 | p + q | +-comm p q
...                                              | refl | _ | refl =
   ub/intro {q = q + q1} a (+-monoʳ-≤ q h1) (ret {eq _ _ _} (eq/intro refl))

ub/bind : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (p : ℂ) (q : val A → ℂ) →
  ub A e p →
  ((a : val A) → ub B (f a) (q a)) →
  ub B (bind {A} (F B) e f)
       (bind {A} (meta ℂ) e (λ a → p + q a))
ub/bind {f = f} p q (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl with h3 a
... | ub/intro {q = q2} b h4 h5 with (f a) | eq/ref h5
... | _ | refl =
  ub/intro {q = q1 + q2} b (+-mono-≤ h1 h4) (ret {eq _ _ _} (eq/intro refl))

ub/bind/const : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (p q : ℂ) →
  ub A e p →
  ((a : val A) → ub B (f a) q) →
  ub B (bind {A} (F B) e f) (p + q)
ub/bind/const {f = f} p q (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl with h3 a
... | ub/intro {q = q2} b h4 h5 with (f a) | eq/ref h5
... | _ | refl =
  ub/intro {q = q1 + q2} b (+-mono-≤ h1 h4) (ret {eq _ _ _} (eq/intro refl))

ub/bind/const' : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (p q : ℂ) → {r : ℂ} →
  p + q ≡ r →
  ub A e p →
  ((a : val A) → ub B (f a) q) →
  ub B (bind {A} (F B) e f) r
ub/bind/const' p q refl h₁ h₂ = ub/bind/const p q h₁ h₂

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
