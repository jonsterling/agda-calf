{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Upper
open import Eq
open import Data.Nat
open import Data.Nat.Properties
open import Connectives
open import Num
open import Relation.Binary.PropositionalEquality as P
open import Data.Nat.Induction
open import Induction
open import Axiom.UniquenessOfIdentityProofs.WithK
open import Relation.Binary.Definitions
open import Function using (const)

open Ext
open iso

ub/ret : ∀ {A a} (n : ℕ) → ub A (ret {A} a) n
ub/ret {A} {a} n = ub/intro {q = 0} a z≤n (ret {eq _ _ _} (eq/intro refl))

-- Need to understand with-abstraction.
ub/step : ∀ {A e} (p q : ℕ) →
  ub A e p →
  ub A (step' (F A) q e) (p + q)
ub/step p q (ub/intro {q = q1} a h1 h2) with eq/ref h2 | p + q | +-comm p q
...                                              | refl | _ | refl =
   ub/intro {q = q + q1} a (+-monoʳ-≤ q h1) (ret {eq _ _ _}(eq/intro refl))

ub/bind : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (h : Ext A) (p : ℕ) (q : Carrier h → ℕ) →
  ub A e p →
  ((a : val A) → ub B (f a) (q (fwd (rep h) a))) →
  ub B (bind {A} (F B) e f)
       (bind {A} (meta ℕ) e (λ a → p + q (fwd (rep h) a)))
ub/bind {f = f} h p q (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl with h3 a
... | ub/intro {q = q2} b h4 h5 with (f a) | eq/ref h5
... | _ | refl =
  ub/intro {q = q1 + q2} b (+-mono-≤ h1 h4) (ret {eq _ _ _} (eq/intro refl))

ub/bind/const : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (h : Ext A) (p q : ℕ) →
  ub A e p →
  ((a : val A) → ub B (f a) q) →
  ub B (bind {A} (F B) e f) (p + q)
ub/bind/const {f = f} h p q (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl with h3 a
... | ub/intro {q = q2} b h4 h5 with (f a) | eq/ref h5
... | _ | refl =
  ub/intro {q = q1 + q2} b (+-mono-≤ h1 h4) (ret {eq _ _ _} (eq/intro refl))

ub/bind/suc : ∀ {A B : tp pos} {e : cmp (F A)} {f : val A → cmp (F B)}
  (h : Ext A) (p : ℕ) →
  ub A e 1 →
  ((a : val A) → ub B (f a) p) →
  ub B (bind {A} (F B) e f) (suc p)
ub/bind/suc {f = f} h p (ub/intro {q = q1} a h1 h2) h3 with eq/ref h2
... | refl with h3 a
... | ub/intro {q = q2} b h4 h5 with (f a) | eq/ref h5
... | _ | refl =
  ub/intro {q = q1 + q2} b (P.subst (λ n → q1 + q2 ≤ n) refl (+-mono-≤ h1 h4)) (ret {eq _ _ _} (eq/intro refl))

if : ∀ {A : ℕ → Set} → (n : ℕ) → (A 0) → ((n : ℕ) → A (suc n)) → A n
if zero n f = n
if (suc m) n f = f m

trans' : ∀ {a} {A : Set a} → Transitive {A = A} _≡_
trans' eq refl = eq

ub/ifz :
  (B : ℕ → tp pos)
  (x : val num)
  (e0 : cmp (F (B 0)))
  (e1 : (y : val num) → suc (to-nat y) ≡ to-nat x → cmp (F (B (suc (to-nat y)))))
  (p1 : ℕ)
  (p2 : ℕ → ℕ) →
  (ub (B 0) e0 p1) →
  ((y : val num) → (h : suc (to-nat y) ≡ to-nat x) → ub (B (suc (to-nat y))) (e1 y h) (p2 (to-nat y))) →
  ub (B (to-nat x)) (ifz (λ n → F (B n)) x e0 e1) (if {λ _ → ℕ} (to-nat x) p1 p2)
ub/ifz B x e0 e1 p1 p2 h1 h2 =
    ifz
        (λ n →
          meta ((h1 : to-nat x ≡ n) →  ub (B (to-nat (to-num n)))
          (ifz (λ n → F (B n)) (to-num n) e0 (λ y h → e1 y (trans' h (symm h1))))
          (if (to-nat (to-num n)) p1 p2))) x
          (λ h → h1)
          (λ y g1 g2 →  h2 y (trans' refl (symm g2)))
          refl