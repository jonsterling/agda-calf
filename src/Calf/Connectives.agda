{-# OPTIONS --prop --rewriting #-}

module Calf.Connectives where

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.PhaseDistinction
open import Calf.Upper
open import Data.Nat
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
import Level as L

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level

bounded : (A : tp pos) → (cmp (meta ℕ)) → tp neg
bounded A n = Σ+- (U (F A)) λ u → ub⁻ A u n

-- used for extracting the extension from a program in order to compute measure/cost
-- information.
-- val A → ℕ
-- val A → Carrier → ℕ
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

proj₁ (fwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  iso.fwd (Ext.rep cA) a
proj₂ (fwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  P.subst (Carrier ∘ cB) (P.sym (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)

proj₁ (bwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
  bwd (rep cA) a
proj₂ (bwd (rep (e/pair {A} {B} cA cB)) (a , b)) =
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
          (P.sym (bwd-fwd (rep cA) (bwd (rep cA) a)))
          (fwd (rep (cB (bwd (rep cA) a)))
           (bwd (rep (cB (bwd (rep cA) a))) b)))

      q =
        H.≡-subst-removable
         (λ a → Carrier (cB a))
         (P.sym (bwd-fwd (rep cA) (bwd (rep cA) a)))
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
          (P.subst (Carrier ∘ cB) (P.sym (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)))

      q = H.≡-subst-removable (Carrier ∘ cB) (P.sym (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)
      r = H.icong (Carrier ∘ cB) (bwd-fwd (rep cA) a) (λ {k} z → bwd (rep (cB k)) z) q
      s = H.≡-to-≅ (bwd-fwd (rep (cB a)) b)

Ψ : (A : tp pos) → (B : val A → tp pos) → (h : Ext A) → (Carrier h → ℕ) → tp neg
Ψ A B h p =
  Σ+- (U(Π A (λ a → F (B a)))) λ f →
    Π A λ a → ub⁻ (B a) (f a) ((p ∘ (iso.fwd (rep h))) a)

lt/cost : ∀ {A} → (h : Ext A) → (p : Carrier h → ℕ) → (val A → val A → Set)
lt/cost h p = _<_ on (p ∘ (iso.fwd (rep h)))

lt/cost/wf : ∀ {A h p} → WellFounded (lt/cost {A} h p)
lt/cost/wf {A} {h} {p} = On.wellFounded (p ∘ (iso.fwd (rep h))) <-wellFounded

e/meta : ∀ A → Ext (U (meta A))
Carrier (e/meta A) = A
fwd (rep (e/meta A)) = id
bwd (rep (e/meta A)) = id
fwd-bwd (rep (e/meta A)) _ = refl
bwd-fwd (rep (e/meta A)) _ = refl

dom : ∀ {ℓ} {a} {A : Set a} {B : Set a} → Rel B ℓ → Rel (A → B) (a L.⊔ ℓ)
dom {A = A} r f1 f2 = ∀ (a : A) → r (f1 a) (f2 a)

pitime/relax : ∀ A B h {p p'} → dom _≤_ p p' →
                 (f : cmp (Ψ A B h p)) →
                 cmp (Ψ A B h p')
pitime/relax A B _ h (func , prf) = func ,
  λ a → ub⁻/decode .fwd (ub/relax (h _) (ub⁻/decode .bwd (prf a)))
