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

pure : tp pos → tp neg 
pure A = Σ+- (U (F A)) λ c → th⁻ (F A) c

bounded : (A : tp pos) → cmp (pure nat) → tp neg
bounded A p = Σ+- (U (F A)) λ u → ub⁻ A u (λ _ → p)

postulate
  ub⁻/code : ∀ {k} → (Â : val (univ pos k)) → cmp (F (el⁺ _ Â)) → cmp 𝒞 → cmp (univ neg k)
  ub⁻/code/decode : ∀ {k} → (Â : val (univ pos k)) → (e : cmp (F (el⁺ _ Â))) → (p : cmp 𝒞) → 
    el⁻ _ (ub⁻/code Â e p) ≡ ub⁻ (el⁺ _ Â) e p
  {-# REWRITE ub⁻/code/decode #-}

bounded/code : ∀ {k} → (val (univ pos k)) → cmp (pure nat) → cmp (univ neg k)
bounded/code Â p = Σ+-/code (Û (F̂ Â)) λ u → ub⁻/code Â u (λ _ → p) 

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
_⇒_[_] : (A : tp pos) → (B : val A → tp pos) → cmp (A ⇒ pure nat) → tp neg
A ⇒ B [ p ] = 
  Σ+- (U(Π A (λ a → F (B a)))) λ f → 
    Π A λ a → ub⁻ _ (f a) (λ _ → p a)

ap/cost : ∀ {A B p} → 
  (f : cmp (A ⇒ B [ p ])) →
  (a : val A) → 
  Σ (cmp (F (B a))) λ b → 
    cmp (ub⁻ _ b (λ _ → p a))
ap/cost (f/fun , f/prf) a = f/fun a , f/prf a 
  
ap/cmp = λ {A} {B} {p} f a → fst (ap/cost {A} {B} {p} f a)
ap/prf = λ {A} {B} {p} f a → snd (ap/cost {A} {B} {p} f a)

ub/ap : ∀ {A B p} → 
  (f : cmp (A ⇒ B [ p ])) →
  (a : val A) → 
  ub (B a) (ap/cmp {A} {B} {p} f a) (λ _ → p a)
ub/ap {A} {B} {p} f a rewrite ub⁻/decode {B a} {ap/cmp {A} {B} {p} f a} {λ _ → p a} = ap/prf {A} {B} {p} f a

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

postulate wf/lt : ∀ {l k} → (h : l < k) → cmp (el⁻ _ (wf {l} {k} h (lift⁺ {k} {0} z≤n nat/code) (lt' {k})))

lt/cost : ∀ {k A} → (p : cmp (A ⇒ pure nat)) → cmp (A ⇒ A ⇒ univ neg k)
lt/cost {k} {A} p a b = lift⁻ z≤n (lt/cmp (p a . fst) (p b . fst))

postulate lt/cost/wf : ∀ {l k Â} → (h : l < k) → 
            (p : cmp (el⁺ _ Â ⇒ pure nat)) → cmp (el⁻ _ (wf h Â (lt/cost {k} {el⁺ _ Â} p)))

fun : ∀ {k} → (Â : val (univ pos (k + 1))) → 
      (B̂ : val (el⁺ _ Â) → val (univ pos k)) → 
      (p : cmp (el⁺ _ Â ⇒ pure nat)) → 
      (body : (a : val (el⁺ _ Â)) → 
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
      in body a' f )) )
