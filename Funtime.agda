{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Eq

bounded : (A : tp pos) → cmp (F nat) → tp neg
bounded A p = Σ+- (U (F A)) λ u → ub⁻ A u (λ _ → p)

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
_⇒_[_] : (A : tp pos) → (B : val A → tp pos) → cmp (A ⇒ F nat) → tp neg
A ⇒ B [ p ] = 
  Σ+- (U(Π A (λ a → F (B a)))) λ f → 
    Π A λ a → ub⁻ _ (f a) (λ _ → p a)

ap : ∀ {A B p} → 
  (f : cmp (A ⇒ B [ p ])) →
  (a : val A) → 
  Σ (cmp (F (B a))) λ b → 
    cmp (ub⁻ _ b (λ _ → p a))
ap (f/fun , f/prf) a = f/fun a , f/prf a 
  
ap/cmp = λ {A} {B} {p} f a → fst (ap {A} {B} {p} f a)
ap/prf = λ {A} {B} {p} f a → snd (ap {A} {B} {p} f a)

ub/ap : ∀ {A B p} → 
  (f : cmp (A ⇒ B [ p ])) →
  (a : val A) → 
  ub (B a) (ap/cmp {A} {B} {p} f a) (λ _ → p a)
ub/ap {A} {B} {p} f a rewrite ub⁻/decode {B a} {ap/cmp {A} {B} {p} f a} {λ _ → p a} = ap/prf {A} {B} {p} f a

-- Need universes to internalize.
wf : (A : tp pos) → (val A → val A → tp pos) → □
wf A R = 
  (P : val A → tp neg) → (a : val A) → 
  ((a : val A) → ((b : val A) → val (R b a) → cmp (P b)) → cmp (P a)) →
  cmp (P a)

postulate wf/lt : wf nat lt

lt/cost : {A : tp pos} → (p : cmp (A ⇒ F nat)) → val A → val A → tp pos 
lt/cost {A} p a b = U(lt/cmp (p a) (p b))

postulate lt/cost/wf : ∀ {A} → (p : cmp (A ⇒ F nat)) → wf A (lt/cost {A} p)

-- Also possible to use subsets to restrict domain?
fun : (A : tp pos) → (B : val A → tp pos) → (p : cmp (A ⇒ F nat)) → 
  (body : (a : val A) → 
          (f : cmp ((Σ++ A (λ a' → lt/cost {A} p a' a)) ⇒ (λ s → B (fst s)) [ (λ s → p (fst s)) ])) → 
          cmp (bounded (B a) (p a))) → 
  cmp (A ⇒ B [ p ])
fun A B p body = 
  (λ a → 
    fst (lt/cost/wf {A} p (λ a → (bounded (B a) (p a))) a 
      (λ a' h → 
       let f : cmp ((Σ++ A (λ a'' → lt/cost {A} p a'' a')) ⇒ (λ s → B (fst s)) [ (λ s → p (fst s)) ]) 
           f = (λ s → fst (h (fst s) (snd s))) , λ s → snd (h (fst s) (snd s))  
       in body a' f)) ) , 
  λ a → snd (lt/cost/wf {A} p (λ a → (bounded (B a) (p a))) a 
    (λ a' h → 
       let f : cmp ((Σ++ A (λ a'' → lt/cost {A} p a'' a')) ⇒ (λ s → B (fst s)) [ (λ s → p (fst s)) ]) 
           f = (λ s → fst (h (fst s) (snd s))) , λ s → snd (h (fst s) (snd s))
       in body a' f )) 