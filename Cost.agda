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
  {-# REWRITE step'/id #-}
  step'/concat : ∀ {B e p q} → 
    step' B p (step' B q e) ≡ step' B (p ⊕ q) e
  {-# REWRITE step'/concat #-}

-- Arithmetic. This can be defined as an inductive type if that is available. 
-- Otherwise it can also be a type computation, which requires universes. 
postulate
  le : val nat → val nat → tp pos
  le/zero : ∀ {n} → val (le zero n)

  lt : val nat → val nat → tp pos

le/cmp : cmp (F nat) → cmp (F nat) → tp neg 
le/cmp c1 c2 = 
  tbind c1 λ n1 → 
  tbind c2 λ n2 → 
  F(le n1 n2)

le/ext : cmp 𝒞 → cmp 𝒞 → tp neg
le/ext p q = ext/cmp (λ u → le/cmp (p u) (q u))

lt/cmp : cmp (F nat) → cmp (F nat) → tp neg 
lt/cmp c1 c2 = 
  tbind c1 λ n1 → 
  tbind c2 λ n2 → 
  F(lt n1 n2)

lt/ext : cmp 𝒞 → cmp 𝒞 → tp neg
lt/ext p q = ext/cmp (λ u → lt/cmp (p u) (q u))
-- Just assume arithmetic is true. Equations should be expressed using an equality type, but since 
-- I am using equality reflection this is equivalent.
postulate
  add/comm : ∀ {n m : val nat} → add n m ≡ add m n
  le/add : ∀ {n1 n2 m1 m2} → val (le n1 m1) → val (le n2 m2) → cmp (le/cmp (add n1 n2) (add m1 m2))

-- This doesn't follow from le/add; dbind needs to record more info...
-- le/add/cmp : ∀ {c1 c2 d1 d2} → cmp (le/cmp c1 d1) → cmp (le/cmp c2 d2) → cmp (le/cmp (add/cmp c1 c2) (add/cmp d1 d2)) 
-- le/add/cmp {c1} {c2} {d1} {d2} h1 h2 = 
--   dbind _ c1 λ n1 → 
--   dbind _ c2 λ n2 → 
--   dbind _ (add n1 n2) λ z1 →
--   dbind _ d1 λ m1 → 
--   dbind _ d2 λ m2 →
--   dbind _ (add m1 m2) λ z2 → {! ?  !}
     
postulate 
  le/add/cmp : ∀ {c1 c2 d1 d2} → cmp (le/cmp c1 d1) → cmp (le/cmp c2 d2) → cmp (le/cmp (add/cmp c1 c2) (add/cmp d1 d2)) 
  add/comm/cmp : ∀ {c1 c2} → add/cmp c1 c2 ≡ add/cmp c2 c1 
  le/refl/cmp : ∀ {c} → cmp (le/cmp c c)

le/add/ext : ∀ {p1 p2 q1 q2} → cmp (le/ext p1 q1) → cmp (le/ext p2 q2) → cmp (le/ext (p1 ⊕ p2) (q1 ⊕ q2)) 
le/add/ext {p1} {p2} {q1} {q2} h1 h2 = λ u → le/add/cmp {c1 = p1 u} {c2 = p2 u} {d1 = q1 u} {d2 = q2 u} (h1 u) (h2 u)

add/comm/ext : ∀ {p q} → p ⊕ q ≡ q ⊕ p 
add/comm/ext {p} {q} = funext/Ω λ u → add/comm/cmp {c1 = p u} {c2 = q u}

le/refl/ext : ∀ {p} → cmp (le/ext p p)
le/refl/ext {p} = λ u → le/refl/cmp {p u}
