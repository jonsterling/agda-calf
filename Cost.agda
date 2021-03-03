{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Eq
open import Thunkable
open import Univ
open import Nat
open import Data.Product.Properties
open import Function.Bundles

infixr 10 _⇒_ 
_⇒_ : tp pos → tp neg → tp neg
A ⇒ B = Π A (λ _ → B)

add : cmp (Π nat (λ _ → Π nat (λ _ → F nat)))
add = λ n → λ m → rec n (λ _ → F nat) (ret m) (λ _ r → bind (F nat) r  λ k → ret(suc k)) 

add/th : ∀ {n1 n2} → th (F nat) (add n1 n2) 
add/th {n1} {n2} = (th/rec n1 (λ _ → nat) (ret n2) ((λ _ r → bind (F nat) r  λ k → ret(suc k))) 
  (th/ret n2) (λ n r h →  th/bind r (λ k → ret(suc k)) h λ a → th/ret _))

add/cmp : cmp (U(F nat) ⇒ U(F nat) ⇒ F nat)
add/cmp = 
  λ c1 c2 → 
  bind (F nat) c1 λ n1 → 
  bind (F nat) c2 λ n2 → 
  add n1 n2 

add/cmp/th : ∀ {c1 c2} → th (F nat) c1 → th (F nat) c2 → th (F nat) (add/cmp c1 c2) 
add/cmp/th {c1} {c2} h1 h2 = 
  (th/bind _ _ h1 (λ n1 → th/bind _ _ h2 (λ n2 → add/th)))

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

-- cost is an extensional computation of a nat with the proof that it is thunkable
𝒞 = ◯⁻(Σ+- (U (F nat)) λ c → th⁻ (F nat) c)

add/cost : cmp (U 𝒞 ⇒ U 𝒞 ⇒ 𝒞)
add/cost c1 c2 u = add/cmp (c1 u . fst) (c2 u . fst)  ,  add/cmp/th (c1 u . snd) (c2 u . snd)

_⊕_ = add/cost

postulate
  step' : ∀ (B : tp neg) → cmp 𝒞 → cmp B → cmp B 
  step'/id : ∀ {B : tp neg} {e : cmp B} → 
    step' B (λ _ → ret zero , th/ret zero) e ≡ e 
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

-- le/ext : cmp 𝒞 → cmp 𝒞 → tp neg
-- le/ext p q = ext/cmp (λ u → le/cmp (p u) (q u))

-- lt/cmp : cmp (F nat) → cmp (F nat) → tp neg 
-- lt/cmp c1 c2 = 
--   tbind c1 λ n1 → 
--   tbind c2 λ n2 → 
--   F(lt n1 n2)

-- lt/ext : cmp 𝒞 → cmp 𝒞 → tp neg
-- lt/ext p q = ext/cmp (λ u → lt/cmp (p u) (q u))
-- Just assume arithmetic is true. Equations should be expressed using an equality type, but since 
-- I am using equality reflection this is equivalent.
postulate
  add/comm : ∀ {n m : val nat} → add n m ≡ add m n
  le/add : ∀ {n1 n2 m1 m2} → val (le n1 m1) → val (le n2 m2) → cmp (le/cmp (add n1 n2) (add m1 m2))
  le/refl : ∀ {n} → val (le n (suc n))

-- this doesn't work because agda decodes the type code when I rewrite the thunkability 
-- equation, which makes the equation inapplicable to the goal. At least this is what I 
-- think is happening.
-- add/comm/cmp : ∀ {c1 c2} → th (F nat) c1 → th (F nat) c2 → 
--   cmp (el⁻ 0 (F̂ (eq/code (Û (F̂ nat/code)) (add/cmp c1 c2) (add/cmp c2 c1))))
-- add/comm/cmp {c1} {c2} h1 h2 = let h = th/thunkable _ h1 {X = univ neg 0} (λ c1 → (F̂ (eq/code (Û (F̂ nat/code)) (add/cmp c1 c2) (add/cmp c2 c1))))
-- in {!  !}

-- this works :)
add/comm/cmp : ∀ {c1 c2} → th (F nat) c1 → th (F nat) c2 → 
  cmp (F (eq (U (F nat)) (add/cmp c1 c2) (add/cmp c2 c1)))
add/comm/cmp {c1} {c2} h1 h2 with F (eq (U (F nat)) (add/cmp c1 c2) (add/cmp c2 c1)) | symm (th/thunkable/tp _ h1 (λ c1 → F (eq (U (F nat)) (add/cmp c1 c2) (add/cmp c2 c1)))) 
... | _ | refl with (tbind c1 λ n1 → F (eq (U (F nat)) (add/cmp (ret n1) c2) (add/cmp c2 (ret n1)))) | symm (th/thunkable/tp _ h2 (λ c2 → tbind c1 λ n1 → F (eq (U (F nat)) (add/cmp (ret n1) c2) (add/cmp c2 (ret n1)))))  
...               | _ | refl = 
  dbind _ c2 λ n2 → 
  dbind _ c1 λ n1 → 
  ret (eq/intro add/comm)
     
-- Requires equality reflection on computations of eq, since 
-- equality of (pure) nat computations is itself a computation.
add/comm/cost : ∀ {p q} → cmp (F (eq (U 𝒞) (p ⊕ q) (q ⊕ p)))
add/comm/cost {p} {q} = 
  (ret (eq/intro (funext/Ω (λ u → Inverse.f Σ-≡,≡↔≡ 
    (eq/ref (add/comm/cmp {p u . fst} {q u . fst} (p u . snd) (q u . snd)) , th/uni _ _)))))
-- postulate 
--   le/add/cmp : ∀ {c1 c2 d1 d2} → cmp (le/cmp c1 d1) → cmp (le/cmp c2 d2) → cmp (le/cmp (add/cmp c1 c2) (add/cmp d1 d2)) 
--   le/refl/cmp : ∀ {c} → cmp (le/cmp c c)

-- le/add/ext : ∀ {p1 p2 q1 q2} → cmp (le/ext p1 q1) → cmp (le/ext p2 q2) → cmp (le/ext (p1 ⊕ p2) (q1 ⊕ q2)) 
-- le/add/ext {p1} {p2} {q1} {q2} h1 h2 = λ u → le/add/cmp {c1 = p1 u} {c2 = p2 u} {d1 = q1 u} {d2 = q2 u} (h1 u) (h2 u)

-- le/refl/ext : ∀ {p} → cmp (le/ext p p)
-- le/refl/ext {p} = λ u → le/refl/cmp {p u}
