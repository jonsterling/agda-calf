{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Eq
open import Thunkable
open import Nat 
open import Univ
open import Data.Nat

enat = ◯⁻ (F nat)

bounded : (A : tp pos) → cmp enat → tp neg
bounded A p = Σ+- (U (F A)) λ u → ub⁻ A u p

postulate
  ub⁻/code : ∀ {k} → (Â : val (univ pos k)) → cmp (F (el⁺ _ Â)) → cmp 𝒞 → cmp (univ neg k)
  ub⁻/code/decode : ∀ {k} → (Â : val (univ pos k)) → (e : cmp (F (el⁺ _ Â))) → (p : cmp 𝒞) → 
    el⁻ _ (ub⁻/code Â e p) ≡ ub⁻ (el⁺ _ Â) e p
  {-# REWRITE ub⁻/code/decode #-}

bounded/code : ∀ {k} → (val (univ pos k)) → cmp enat → cmp (univ neg k)
bounded/code Â p = Σ+-/code (Û (F̂ Â)) λ u → ub⁻/code Â u p

in⁺ : (A : tp pos) → val A → val (◯⁺ A)
in⁺ A a = λ _ → a

force : ∀ {A} → val (U (F A)) → cmp (F A)
force {A} u = bind (F A) u (λ v → ret v)


-- Decomposing funtime as Π and bounded seems complicated, 
-- because of the apparent need to suspend the computed result 
-- in the definition of bounded elements, which means we have to 
-- check that the suspended computation is computed immediately as 
-- well.
-- A => B [ p ] consists of a function from a : A 
-- bounded (B a) (p a) and a proof that this function 
-- returns immediately.
-- _⇒_[_] : (A : tp pos) → (B : val A → tp pos) → cmp ((◯⁺ A) ⇒ 𝒞) → tp neg
-- A ⇒ B [ p ] = 
--   Σ+- (U(Π A (λ a → F (bounded (B a) (p (in⁺ A a)))))) λ f → 
--     Π A λ a → ub⁻ _ (f a) (λ _ → ret zero)

-- Direct definition
_⇒_[_] : (A : tp pos) → (B : val A → tp pos) → cmp (A ⇒ enat) → tp neg
A ⇒ B [ p ] = 
  Σ+- (U(Π A (λ a → F (B a)))) λ f → 
    Π A λ a → ub⁻ _ (f a) (p a)

ap/cost : ∀ {A B p} → 
  (f : cmp (A ⇒ B [ p ])) →
  (a : val A) → 
  Σ (cmp (F (B a))) λ b → 
    cmp (ub⁻ _ b (p a))
ap/cost (f/fun , f/prf) a = f/fun a , f/prf a 
  
ap/cmp = λ {A} {B} {p} f a → fst (ap/cost {A} {B} {p} f a)
ap/prf = λ {A} {B} {p} f a → snd (ap/cost {A} {B} {p} f a)

ub/ap : ∀ {A B p} → 
  (f : cmp (A ⇒ B [ p ])) →
  (a : val A) → 
  ub (B a) (ap/cmp {A} {B} {p} f a) (p a)
ub/ap {A} {B} {p} f a rewrite ub⁻/decode {B a} {ap/cmp {A} {B} {p} f a} {p a} = ap/prf {A} {B} {p} f a

-- Need universes to internalize.
-- wf : (A : tp pos) → (val A → val A → tp pos) → □
-- wf A R = 
--   (P : val A → tp neg) → (a : val A) → 
--   ((a : val A) → ((b : val A) → val (R b a) → cmp (P b)) → cmp (P a)) →
--   cmp (P a)
_⇒̂_ : ∀ {k} → val(univ pos k) → cmp (univ neg k) → cmp (univ neg k)
A ⇒̂ B = Π̂ A λ _ → B

-- remove when I find this in the std-lib 
postulate 
  a1 : ∀ {l k} → l < k → l ≤ k
  a2 : ∀ {k} → k < k + 1

-- carriers at level k, properties at level l < k.
wf : ∀ {l k} → l < k → cmp (Π (univ pos k) λ Â → U (el⁺ _ Â ⇒ el⁺ _ Â ⇒ univ neg k) ⇒ univ neg k)
wf {l} {k} h = λ Â R → 
  Π̂ (Û (Â ⇒̂ Û⁻ h)) λ P →
  Π̂ Â λ a → 
  Û(Π̂ Â λ a → 
    Û(Π̂ Â λ b → (Û (R b a)) ⇒̂ lift⁻ {k} {l} (a1 h) (P b)) ⇒̂ lift⁻ (a1 h) (P a)) ⇒̂ 
 lift⁻ (a1 h) (P a)  

lt' : ∀ {k} → cmp (nat ⇒ nat ⇒ univ neg k)
lt' {k} = λ n m → lift⁻ (z≤n) (lt n m)

lt'/cmp : ∀ {k} → cmp (U (pure nat) ⇒ U (pure nat) ⇒ univ neg k)
lt'/cmp {k} = λ c1 c2 → lift⁻ (z≤n) (lt/cmp c1 c2)

 -- strive to define predicates on extensional types and 
 -- functions returning extensional types
lt/ext : ∀ {k} → cmp (U enat ⇒ U enat ⇒ univ neg k)
lt/ext {k} e1 e2 = 
  ext/cmp/code λ u → 
  bind (univ neg k) (e1 u) λ n1 → 
  bind (univ neg k) (e2 u) λ n2 → 
  lift⁻ (z≤n) (lt n1 n2)

postulate 
  wf/lt : ∀ {l k} → (h : l < k) → cmp (el⁻ _ (wf {l} {k} h (lift⁺ {k} {0} z≤n nat/code) (lt' {k})))
  wf/lt/cmp : ∀ {l k} → (h : l < k) → cmp (el⁻ _ (wf {l} {k} h (lift⁺ {k} {0} z≤n (Û (pure/code nat/code))) (lt'/cmp {k})))

lt/cost : ∀ {k A} → (p : cmp (A ⇒ enat)) → cmp (A ⇒ A ⇒ univ neg k)
lt/cost {k} {A} p a b = lift⁻ z≤n (lt/ext (p a) (p b))

postulate 
  lt/cost/wf : ∀ {l k Â} → (h : l < k) → 
            (p : cmp (el⁺ _ Â ⇒ enat)) → cmp (el⁻ _ (wf h Â (lt/cost {k} {el⁺ _ Â} p)))

fun : ∀ {k} → 
      (Â : val (univ pos (k + 1))) → 
      (B̂ : val (el⁺ _ Â) → val (univ pos k)) → 
      (p : cmp (el⁺ _ Â ⇒ enat)) → 
      (body : (a : val (el⁺ _ Â)) → 
      -- self takes in a value of A, with proof that it induces lower cost. 
      -- proof should be in the extensional fragment.
              (self : cmp ((Σ++ (el⁺ _ Â) (λ a' → U (el⁻ _ (lt/cost {k + 1} {el⁺ _ Â} p a' a)))) ⇒ (λ s → el⁺ _ (B̂ (fst s))) [ (λ s → p (fst s)) ] )) → 
              cmp (el⁻ _ (bounded/code (B̂ a) (p a)))) → 
      cmp ((el⁺ _ Â) ⇒ (λ a → el⁺ _ (B̂ a)) [ p ])
fun {k} Â B̂ p body = 
  (λ a → 
    fst (lt/cost/wf {k} {k + 1} {Â} a2 p (λ a → bounded/code (B̂ a) (p a)) a 
      (λ a' h → 
      let f : cmp ((Σ++ (el⁺ _ Â) (λ a'' → U (el⁻ _ (lt/cost {k + 1} {el⁺ _ Â} p a'' a')))) ⇒ (λ s → el⁺ _ (B̂ (fst s))) [ (λ s → p (fst s)) ]) 
          f = (λ s → fst (h (fst s) (snd s))) , λ s → snd (h (fst s) (snd s))  
      in body a' f )) ) , 
  (λ a → 
    snd (lt/cost/wf {k} {k + 1} {Â} _ p (λ a → bounded/code (B̂ a) (p a)) a 
      (λ a' h → 
      let f : cmp ((Σ++ (el⁺ _ Â) (λ a'' → U (el⁻ _ (lt/cost {k + 1} {el⁺ _ Â} p a'' a')))) ⇒ (λ s → el⁺ _ (B̂ (fst s))) [ (λ s → p (fst s)) ]) 
          f = (λ s → fst (h (fst s) (snd s))) , λ s → snd (h (fst s) (snd s))  
      in body a' f )))

_×_ : tp pos → tp pos → tp pos 
A × B = Σ++ A λ _ → B 

_⊗_ : tp pos → tp pos → tp neg
A ⊗ B = Σ+- (U (F A)) λ _ → (F B) 

_×̂_ : ∀ {k} → val (univ pos k) → val (univ pos k) → val (univ pos k)
Â ×̂ B̂ = Σ++/code Â λ _ → B̂

_⊗̂_ : ∀ {k} → val (univ pos k) → val (univ pos k) → cmp (univ neg k)
Â ⊗̂ B̂ = Σ+-/code (Û (F̂ Â)) λ _ → (F̂ B̂)

_&_ : tp neg → tp neg → tp neg
X & Y = Σ+- (U X) λ _ → Y

_&̂_ : ∀ {k} → cmp (univ neg k) → cmp (univ neg k) → cmp (univ neg k)
X̂ &̂ Ŷ = Σ+-/code (Û X̂) λ _ → Ŷ

pure/nat : val nat → cmp (pure nat)
pure/nat n = ret n , th/ret n

pure/nat/suc : cmp (pure nat) → cmp (pure nat)
pure/nat/suc c = (bind (F nat) (c . fst) λ n → ret (Nat.suc n)) , th/bind _ _ (c . snd) (λ a → th/ret _)

fun/code : 
  (A : tp pos) → 
  (B : val A → tp pos) → 
  (p : cmp (A ⇒ enat)) → 
  cmp (A ⇒ B [ p ]) → 
  cmp (Π A (λ a → F (B a))) 
fun/code A B p f = f . fst 

fun/cost : 
  (A : tp pos) → 
  (B : val A → tp pos) → 
  (p : cmp (A ⇒ enat)) → 
  (f : cmp (A ⇒ B [ p ])) → 
  cmp (Π A (λ a → ub⁻ (B a) (fun/code A B p f a) (p a))) 
fun/cost A B p f = f . snd

postulate
  gt : cmp (nat ⇒ nat ⇒ univ neg 0)
  gt/zero : ∀ {n} → cmp (el⁻ _ (gt (Nat.suc n) Nat.zero))

-- specification for modulus
mod/nat/valid : cmp (nat × nat ⇒ univ neg 0)
mod/nat/valid = λ (m , n) → gt n Nat.zero

mod/nat/valid/cmp : cmp (U (pure nat & pure nat) ⇒ univ neg 0)
mod/nat/valid/cmp ((c1 , _) , (c2 , _)) = 
  bind (univ neg 0) c1 λ n1 → 
  bind (univ neg 0) c2 λ n2 → 
  mod/nat/valid (n1 , n2) 

-- specification of a mathematical function. Must be pure
postulate
  mod/nat : cmp (Σ++ (nat × nat) (λ p → U (el⁻ _ (mod/nat/valid p))) ⇒ pure nat)

-- FU trick, because thunkability targets F's.
mod/nat/cmp' : cmp (Π (U (pure nat) × U (pure nat)) (λ p → 
  F(U(U(el⁻ _ (mod/nat/valid/cmp p)) ⇒ pure nat))))
mod/nat/cmp' p with F(U(U(el⁻ _ (mod/nat/valid/cmp p)) ⇒ pure nat)) | symm (th/thunkable/tp {nat} (p .fst .fst) (p . fst . snd) (λ c → 
  F(U(U (el⁻ _ (
  bind (univ neg 0) c λ n1 →  
  bind (univ neg 0) (p . snd . fst) λ n2 →  
  mod/nat/valid (n1 , n2))) ⇒ pure nat))))
... | _ | refl with (tbind (p .fst .fst) λ n1 → F(U(U (el⁻ _ (
  bind {nat} (univ neg 0) (ret n1) λ n1 →  
  bind (univ neg 0) (p . snd . fst) λ n2 →  
  mod/nat/valid (n1 , n2))) ⇒ pure nat))) | symm (th/thunkable/tp {nat} (p .snd .fst) (p . snd . snd) (λ c → 
  tbind (p .fst .fst) λ n1 →
  F(U(U (el⁻ _ (
  bind {nat} (univ neg 0) (ret n1) λ n1 →  
  bind (univ neg 0) c λ n2 →  
  mod/nat/valid (n1 , n2))) ⇒ pure nat)))) 
... | _ | refl = 
  dbind _ (p .snd .fst) λ n2 →
  dbind _ (p .fst .fst) λ n1 →  ret (λ h → mod/nat ((n1 , n2) , h))

mod/nat/cmp : cmp (Π (U (pure nat & pure nat)) (λ p → 
  U (el⁻ _ (mod/nat/valid/cmp p)) ⇒ pure nat)) 
mod/nat/cmp p = bind (U (el⁻ _ (mod/nat/valid/cmp p)) ⇒ pure nat) (mod/nat/cmp' p) λ x → x
-- computing with numbers. For simplicity, let's assume there's a constructor that 
-- makes a number from a nat with no cost. We also should be able to compute the denotation of a num.
postulate
  num : tp pos 
  con : cmp (nat ⇒ (λ _ → num) [ (λ _ _ → ret Nat.zero) ])
  -- this indicates that the denotation is computed in a thunkable way
  de : cmp (num ⇒ enat)

-- modulus on num
mod/num/valid : cmp (num × num ⇒ univ neg 0)
mod/num/valid = λ (m , n) → 
  ext/cmp/code λ u →
  bind (univ neg 0) (de m u) λ n1 → 
  bind (univ neg 0) (de n u) λ n2 → 
  mod/nat/valid (n1 , n2)

-- takes one step per application. 
-- coherence means mod commutes with the denotation of num in the expected way.
postulate
  mod/num : cmp (Σ++ (num × num) (λ p → U (el⁻ _ (mod/num/valid p))) ⇒ (λ _ → num) [ (λ _ _ → ret (Nat.suc Nat.zero)) ])
  -- mod/coh : cmp (Π (Σ++ (num × num) (λ p → U (el⁻ _ (mod/num/valid p)))) λ p → 
  --           F (eq (U (pure nat)) 
  --             (de/pure/cmp (fun/code 
  --               (Σ++ (num × num) (λ p → U (el⁻ _ (mod/num/valid p)))) 
  --               (λ _ → num) 
  --               (λ _ _ → ret (Nat.suc Nat.zero)) 
  --               mod/num p))  
  --             (mod/nat/cmp (de/pure (p . fst . fst) , de/pure (p . fst . snd)) (p . snd) )))

postulate
  lt/mod : ∀ {m n} → (h : cmp (el⁻ _ (mod/nat/valid (m , n)))) → 
    cmp (el⁻ _ (lt/cmp (mod/nat ((m , n) , h)) (pure/nat n)))
  lt/mod/cmp : ∀ {c1 c2} → (h : cmp (el⁻ _ (mod/nat/valid/cmp (c1 , c2)))) → 
    cmp (el⁻ _ (lt/cmp (mod/nat/cmp (c1 , c2) h) c2 ))
  
-- Unlikely to work out. Should lift everything to the computation layer.
-- nat/mod/lt : cmp (Π (Σ++ (nat × nat) (λ p → U (el⁻ _ (mod/nat/valid p)))) λ ((m , n) , h) →  
-- Σ+- nat (λ k → el⁻ _ (lt k n)))

-- gcd (m,n) requires n < m
gcd/valid/code : val (nat × nat) → cmp (univ neg 0)
gcd/valid/code = λ (m , n) → lt n m

postulate
  ext/compat : ∀ {A} → (u : ext) → (t : cmp (◯⁻ (F A))) → (f : cmp (◯⁻ (F A)) → tp neg) → 
    f t ≡ (tbind (t u) λ a → f (λ _ → ret a))


gcd/valid/cmp/code : cmp (enat & enat) → cmp (univ neg 0)
gcd/valid/cmp/code (e1 , e2) = 
  ext/cmp/code λ u → 
  bind (univ neg 0) (e2 u) λ n2 → 
  bind (univ neg 0) (e1 u) λ n1 → 
  gcd/valid/code (n1 , n2)

gcd/valid/cmp : cmp (enat & enat) → tp neg
gcd/valid/cmp p = el⁻ _ (gcd/valid/cmp/code p)

gcd/cost/in/code = Û (Σ+-/code (Û (◯⁻/code (F̂ nat/code) &̂ ◯⁻/code (F̂ nat/code))) gcd/valid/cmp/code)

gcd/cost/in = el⁺ _ gcd/cost/in/code

lt/ext/prod : ∀ {k} → cmp (gcd/cost/in ⇒ gcd/cost/in ⇒ univ neg k)
lt/ext/prod {k} ((e1 , e2) , _) ((d1 , d2) , _) = 
  lift⁻ (z≤n) (lt/ext e1 d1 &̂ lt/ext e2 d2)

postulate
  wf/lt/prod : ∀ {l k} → (h : l < k) → 
    cmp (el⁻ _ (wf {l} {k} h (lift⁺ z≤n gcd/cost/in/code) lt/ext/prod))

postulate
  mod/nat/ext : cmp (Σ++ (nat × nat) (λ p → U (el⁻ _ (mod/nat/valid p))) ⇒ enat)

postulate
  lt/mod/ext : ∀ {m n} → (h : cmp (el⁻ 0 (mod/nat/valid (m , n)))) → 
    cmp (el⁻ 0 (lt/ext (mod/nat/ext ((m , n) , h)) (λ _ → ret n)))
-- first define a recurrence relation such that gcd refines it. 
ih' : ∀ {e1 e2} → ext → cmp(F(U(
       Π (U(gcd/valid/cmp (e1 , e2))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x ((e1 , e2) , p))) ⇒ enat) 
          ⇒ enat))))
ih' {e1} {e2} u with F(U(
       Π (U(gcd/valid/cmp (e1 , e2))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x ((e1 , e2) , p))) ⇒ enat) 
          ⇒ enat))) | ext/compat u e1 (λ e → F(U(
       Π (U(gcd/valid/cmp (e , e2))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x ((e , e2) , p))) ⇒ enat) 
          ⇒ enat))))
... | _ | refl with (tbind (e1 u) λ n1 → F(U(
       Π (U(gcd/valid/cmp ((λ _ → ret n1)  , e2))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x (((λ _ → ret n1) , e2) , p))) ⇒ enat) 
          ⇒ enat)))) | ext/compat u e2 (λ e → tbind (e1 u) λ n1 → F(U(
       Π (U(gcd/valid/cmp ((λ _ → ret n1)  , e))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x (((λ _ → ret n1) , e) , p))) ⇒ enat) 
          ⇒ enat)))) 
... | _ | refl  = 
  dbind _ (e2 u) λ n2 → 
  dbind _ (e1 u) λ n1 → 
  ret 
    (rec n2 
    (λ n → 
      Π (U(gcd/valid/cmp ((λ _ → ret n1)  , (λ _ → ret n)))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U(el⁻ 0 (lt/ext/prod x (((λ _ → ret n1) , (λ _ → ret n)) , p))) ⇒ enat) 
          ⇒ enat))
    (λ p h → λ _ → ret Nat.zero)
    (λ n2' _ → λ p h → h (((λ _ → ret (Nat.suc n2')) , mod/nat/ext ((n1 , (Nat.suc n2')) , gt/zero)) , lt/mod/ext gt/zero) (p , lt/mod/ext gt/zero))) 

ih : ∀ {e1 e2} → ext → cmp(
       Π (U(gcd/valid/cmp (e1 , e2))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x ((e1 , e2) , p))) ⇒ enat) 
          ⇒ enat))
ih {e1} {e2} u = bind (Π (U(gcd/valid/cmp (e1 , e2))) λ p → 
       (U(Π gcd/cost/in λ x → 
        U (el⁻ 0 (lt/ext/prod x ((e1 , e2) , p))) ⇒ enat) 
          ⇒ enat)) (ih' {e1} {e2} u) λ x → x

gcd/cost : cmp (gcd/cost/in ⇒ enat)
gcd/cost = λ { i →  
  wf/lt/prod {0} {1} (s≤s z≤n) (λ x → ◯⁻/code (F̂ nat/code)) i
  λ ((e1 , e2) , p) → λ h u →  (ih {e1} {e2} u p h) u
  }
