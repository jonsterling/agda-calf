{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Data.Nat using (ℕ; _+_; _<_)
open import Relation.Binary
open import Level using (Level; _⊔_)
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Data.Nat.Induction
open import Function.Base
import Relation.Binary.PropositionalEquality as P
import Relation.Binary.HeterogeneousEquality as H
open import Data.Product.Properties
open import Function.Bundles
open import Induction

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level

bounded : (A : tp pos) → (cmp (F nat)) → tp neg
bounded A n = Σ+- (U (F A)) λ u → ub⁻ A u n

-- used for extracting the extension from a program in order to compute measure/cost
-- information.
record Ext (A : tp pos) : Set₁ where
  field
    Carrier : Set
    rep : iso (val A) Carrier

open Ext
open iso

e/pair : ∀ {A B} →
  (cA : Ext A) →
  (cB : (a : val A) → Ext (B a)) →
  Ext (Σ++ A B)

Carrier (e/pair {A} {B} cA cB) =
  Σ (Carrier cA) (λ a → Carrier (cB (bwd (rep cA) a)))

fst (fwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  iso.fwd (Ext.rep cA) a
snd (fwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  P.subst (Carrier ∘ cB) (symm (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)

fst (bwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  bwd (rep cA) a
snd (bwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  bwd (rep (cB (bwd (rep cA) a))) b

fwd-bwd (rep (e/pair {A} {B} cA cB)) (a , b) =
  Inverse.f Σ-≡,≡↔≡
    (fwd-bwd (rep cA) a ,
     H.≅-to-≡ (H.trans p (H.trans q (H.≡-to-≅ (fwd-bwd (rep (cB _)) b)))))
  where
    abstract
      p =
        H.≡-subst-removable
         (λ a → Carrier (cB (bwd (rep cA) a)))
         (fwd-bwd (rep cA) a)
         (P.subst (λ a → Carrier (cB a))
          (symm (bwd-fwd (rep cA) (bwd (rep cA) a)))
          (fwd (rep (cB (bwd (rep cA) a)))
           (bwd (rep (cB (bwd (rep cA) a))) b)))

      q =
        H.≡-subst-removable
         (λ a → Carrier (cB a))
         (symm (bwd-fwd (rep cA) (bwd (rep cA) a)))
         (fwd (rep (cB (bwd (rep cA) a)))
          (bwd (rep (cB (bwd (rep cA) a))) b))

bwd-fwd (rep (e/pair {A} {B} cA cB)) (a , b) =
  Inverse.f Σ-≡,≡↔≡
    (bwd-fwd (rep cA) a ,
     H.≅-to-≡ (H.trans p (H.trans r s)))
  where
    abstract
      p =
        H.≡-subst-removable
         (val ∘ B)
         (bwd-fwd (rep cA) a)
         (bwd
          (rep (cB (bwd (rep cA) (fwd (rep cA) a))))
          (P.subst (Carrier ∘ cB) (symm (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)))

      q = H.≡-subst-removable (Carrier ∘ cB) (symm (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)
      r = H.icong (Carrier ∘ cB) (bwd-fwd (rep cA) a) (λ {k} z → bwd (rep (cB k)) z) q
      s = H.≡-to-≅ (bwd-fwd (rep (cB a)) b)

_⇒_[_,_] : (A : tp pos) → (B : val A → tp pos) → (h : Ext A) → (Carrier h → ℕ) → tp neg
A ⇒ B [ h , p ] =
  Σ+- (U(Π A (λ a → F (B a)))) λ f →
    Π A λ a → ub⁻ (B a) (f a) ((p ∘ (iso.fwd (rep h))) a)

lt/cost : ∀ {A} → (h : Ext A) → (p : Carrier h → ℕ) → (val A → val A → Set)
lt/cost h p = _<_ on (p ∘ (iso.fwd (rep h)))

lt/cost/wf : ∀ {A h p} → WellFounded (lt/cost {A} h p)
lt/cost/wf {A} {h} {p} = On.wellFounded (p ∘ (iso.fwd (rep h))) <-wellFounded

-- place to store meta info about cost internally
postulate
  meta : Set → tp neg
  meta/out : ∀ {A} → val (U(meta A)) ≡ A
  {-# REWRITE meta/out #-}

e/meta : ∀ A → Ext (U (meta A))
Carrier (e/meta A) = A
fwd (rep (e/meta A)) = id
bwd (rep (e/meta A)) = id
fwd-bwd (rep (e/meta A)) _ = refl
bwd-fwd (rep (e/meta A)) _ = refl

-- fun :
--   (A : tp pos) →
--   (h : Ext A) →
--   (B : val A → tp pos) →
--   (p : Ext.𝒜 h → ℕ) →
--   (body : (a : val A) →
--           (self : cmp (Σ++ A λ a' → meta (lt/cost h p a' a) ⇒ (λ s → B (s . fst)) [ h ,  ] ) )
