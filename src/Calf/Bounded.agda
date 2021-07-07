{-# OPTIONS --prop --without-K --rewriting #-}

open import Calf.CostMonoid

module Calf.Bounded (costMonoid : CostMonoid) where

open CostMonoid costMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Eq
open import Calf.Step costMonoid
open import Calf.ExtensionalFragment costMonoid

open import Calf.Types.Bool
open import Calf.Types.Sum

open import Relation.Binary.PropositionalEquality as Eq


record IsBounded (A : tp pos) (e : cmp (F A)) (c : cmp cost) : □ where
  constructor ⇓_withCost_[_,_]
  field
    result : val A
    c' : ℂ
    h-bounded : ◯ (c' ≤ c)
    h-≡ : cmp (F (eq (U (F A)) e (step (F A) c' (ret result))))

IsBounded⁻ : (A : tp pos) → cmp (F A) → cmp cost → tp neg
IsBounded⁻ A e p = meta (IsBounded A e p)

bound/relax : ∀ {A e p p'} → ◯ (p ≤ p') → IsBounded A e p → IsBounded A e p'
bound/relax h (⇓ result withCost c' [ h-bounded , h-≡ ]) = ⇓ result withCost c' [ (λ u → ≤-trans (h-bounded u) (h u)) , h-≡ ]


bound/circ : ∀ {A e} d {c} →
  IsBounded A e c →
  IsBounded A e (step (meta ℂ) d c)
bound/circ d {c} (⇓ a withCost c' [ h-bounded , h-≡ ]) =
  ⇓ a withCost c' [ (λ u → subst (c' ≤_) (sym (step/ext cost c d u)) (h-bounded u)) , h-≡ ]

bound/ret : {A : tp pos} {a : val A} → IsBounded A (ret {A} a) zero
bound/ret {a = a} = ⇓ a withCost zero [ (λ u → ≤-refl) , ret (eq/intro refl) ]

bound/step : ∀ {A e} (d c : ℂ) →
  IsBounded A e c →
  IsBounded A (step (F A) d e) (d + c)
bound/step d c (⇓ a withCost c' [ h-bounded , h-≡ ]) with eq/ref h-≡
... | refl = ⇓ a withCost d + c' [ (λ u → +-monoʳ-≤ d (h-bounded u)) , ret (eq/intro refl) ]

bound/bind : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (c : ℂ) (d : val A → ℂ) →
  IsBounded A e c →
  ((a : val A) → IsBounded B (f a) (d a)) →
  IsBounded B (bind {A} (F B) e f)
              (bind {A} cost e (λ a → c + d a))
bound/bind {f = f} c d (⇓ a withCost c' [ h-bounded₁ , h-≡₁ ]) h with eq/ref h-≡₁
... | refl with h a
... | ⇓ b withCost d' [ h-bounded₂ , h-≡₂ ] with f a | eq/ref h-≡₂
... | _ | refl = bound/circ c' (⇓ b withCost c' + d' [ (λ u → +-mono-≤ (h-bounded₁ u) (h-bounded₂ u)) , ret (eq/intro refl) ])

bound/bind/const : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (c d : ℂ) →
  IsBounded A e c →
  ((a : val A) → IsBounded B (f a) d) →
  IsBounded B (bind {A} (F B) e f) (c + d)
bound/bind/const c d (⇓ a withCost c' [ h-bounded , h-≡ ]) h with eq/ref h-≡
... | refl = bound/circ' c' (bound/bind c (λ _ → d) (⇓ a withCost c' [ h-bounded , h-≡ ]) h)
  where
    bound/circ' : ∀ {A e} d {c} →
      IsBounded A e (step (meta ℂ) d c) →
      IsBounded A e c
    bound/circ' d {c} (⇓ a withCost c' [ h-bounded , h-≡ ]) =
      ⇓ a withCost c' [ (λ u → subst (c' ≤_) (step/ext cost c d u) (h-bounded u)) , h-≡ ]

bound/bool : ∀ {A : tp pos} {e0 e1} {p : val bool → cmp cost} →
  (b : val bool) →
  IsBounded A e0 (p false) →
  IsBounded A e1 (p true ) →
  IsBounded A (if b then e1 else e0) (p b)
bound/bool false h0 h1 = h0
bound/bool true  h0 h1 = h1

bound/sum/case/const/const : ∀ A B (C : val (sum A B) → tp pos) →
  (s : val (sum A B)) →
  (e0 : (a : val A) → cmp (F (C (inj₁ a)))) →
  (e1 : (b : val B) → cmp (F (C (inj₂ b)))) →
  (p : ℂ) →
  ((a : val A) → IsBounded (C (inj₁ a)) (e0 a) p) →
  ((b : val B) → IsBounded (C (inj₂ b)) (e1 b) p) →
  IsBounded (C s) (sum/case A B (λ s → F (C s)) s e0 e1) p
bound/sum/case/const/const A B C s e0 e1 p h1 h2 = sum/case A B
  (λ s → meta (IsBounded (C s) (sum/case A B (λ s₁ → F (C s₁)) s e0 e1) p)) s h1 h2
