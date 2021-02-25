{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction

postulate
  nat : tp pos 
  zero : val nat 
  suc : val nat → val nat
  rec : (n : val nat) → (X : val nat → tp neg) → 
    cmp (X zero) → 
    ((n : val nat) → val (U (X n)) → cmp (X (suc n))) → 
    cmp (X n)

infixr 10 _⇒_ 
_⇒_ : tp pos → tp neg → tp neg
A ⇒ B = Π A (λ _ → B)

add : cmp (Π nat (λ _ → Π nat (λ _ → F nat)))
add = λ n → λ m → rec n (λ _ → F nat) (ret m) (λ _ r → bind (F nat) r  λ k → ret(suc k)) 

add/cmp : cmp (U(F nat) ⇒ U(F nat) ⇒ F nat)
add/cmp = 
  λ c1 c2 → 
  bind (F nat) c1 λ n1 → 
  bind (F nat) c2 λ n2 → 
  add n1 n2 

infix 10 ◯⁺_
infix 10 ◯⁻_
postulate
  ext/val : (ext → tp pos) → tp pos 
  ext/val/decode : ∀ {A} → val (ext/val A) ≡ ∀ (u : ext) → (val (A u))
  {-# REWRITE ext/val/decode #-}

  ext/cmp : (ext → tp neg) → tp neg 
  ext/cmp/decode : ∀ {A} → val (U (ext/cmp A)) ≡ ∀ (u : ext) → (cmp (A u))
  {-# REWRITE ext/cmp/decode #-}

◯⁺_ : tp pos → tp pos
◯⁺ A = ext/val (λ _ → A)
◯⁻_ : tp neg → tp neg
◯⁻ A = ext/cmp (λ _ → A)

infixr 20 _⊕_

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

𝒞 = ◯⁻(F nat)

add/ext : cmp (U(◯⁻(F nat)) ⇒ U(◯⁻(F nat)) ⇒ ◯⁻(F nat))
add/ext c1 c2 u = add/cmp (c1 u) (c2 u)

_⊕_ = add/ext

postulate
  step' : ∀ (B : tp neg) → cmp 𝒞 → cmp B → cmp B 
  step'/id : ∀ {B : tp neg} {e : cmp B} → 
    step' B (λ _ → ret zero) e ≡ e 
  step'/concat : ∀ {B e p q} → 
    step' B p (step' B q e) ≡ step' B (p ⊕ q) e

-- Arithmetic. This can be defined as an inductive type if that is available. 
-- Otherwise it can also be a type computation, which requires universes. 
postulate
  le : val nat → val nat → tp pos 
  le/zero : ∀ {n} → val (le zero n)
  le/succ : ∀ {n m} → val (le n m) → val (le (suc n) (suc m))

le/cmp : cmp (F nat) → cmp (F nat) → tp neg 
le/cmp c1 c2 = 
  tbind c1 λ n1 → 
  tbind c2 λ n2 → 
  F(le n1 n2)

le/ext : cmp 𝒞 → cmp 𝒞 → tp neg
le/ext p q = ext/cmp (λ u → le/cmp (p u) (q u))
