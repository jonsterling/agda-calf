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
e/pair {A} {B} cA cB = record 
  { Carrier = Σ (Carrier cA) λ a → Carrier (cB (bwd (rep cA) a)) 
  ; rep = record 
      { fwd = λ (a , b) → 
        iso.fwd (Ext.rep cA) a , P.subst (λ a → Carrier (cB a)) (symm (bwd-fwd (rep cA) a)) (fwd (rep (cB a)) b)
      ; bwd = λ (a , b) →  bwd (rep cA) a , bwd (rep (cB (bwd (rep cA) a))) b
      ; fwd-bwd = λ x → 
          let e1 = fwd-bwd (rep cA) (fst x) in 
            Inverse.f Σ-≡,≡↔≡ (e1 , e)
      ; bwd-fwd = λ x → Inverse.f Σ-≡,≡↔≡ (bwd-fwd (rep cA) (fst x) , e2)}
  }
  where       
  e' : ∀ {x} → P.subst (λ a → Carrier (cB (bwd (rep cA) a)))
        (fwd-bwd (rep cA) (fst x))
        (P.subst (λ a → Carrier (cB a))
        (symm (bwd-fwd (rep cA) (bwd (rep cA) (fst x))))
        (fwd (rep (cB (bwd (rep cA) (fst x))))
          (bwd (rep (cB (bwd (rep cA) (fst x)))) (snd x))))
        H.≅ snd x 
  e' {x} = 
    let h = H.≡-subst-removable (λ a → Carrier (cB (bwd (rep cA) a))) (fwd-bwd (rep cA) (fst x)) 
          (P.subst (λ a → Carrier (cB a))
          (symm (bwd-fwd (rep cA) (bwd (rep cA) (fst x))))
          (fwd (rep (cB (bwd (rep cA) (fst x))))
            (bwd (rep (cB (bwd (rep cA) (fst x)))) (snd x)))) in 
    let h1 = H.≡-subst-removable (λ a → Carrier (cB a)) 
              (symm (bwd-fwd (rep cA) (bwd (rep cA) (fst x))))
              (fwd (rep (cB (bwd (rep cA) (fst x))))
                (bwd (rep (cB (bwd (rep cA) (fst x)))) (snd x))) in 
    let h2 =  H.≡-to-≅ (fwd-bwd (rep (cB (bwd (rep cA) (fst x)))) (snd x)) in 
   H.trans h (H.trans h1 h2)

  e : ∀ {x} → P.subst (λ a → Carrier (cB (bwd (rep cA) a)))
        (fwd-bwd (rep cA) (fst x))
        (P.subst (λ a → Carrier (cB a))
        (symm (bwd-fwd (rep cA) (bwd (rep cA) (fst x))))
        (fwd (rep (cB (bwd (rep cA) (fst x))))
          (bwd (rep (cB (bwd (rep cA) (fst x)))) (snd x))))
        ≡ snd x 
  e {x} = H.≅-to-≡ e'

  e2' : ∀ {x} → P.subst (λ x₁ → val (B x₁)) (bwd-fwd (rep cA) (fst x))
    (bwd (rep (cB (bwd (rep cA) (fwd (rep cA) (fst x)))))
     (P.subst (λ a → Carrier (cB a)) (symm (bwd-fwd (rep cA) (fst x)))
      (fwd (rep (cB (fst x))) (snd x))))
    H.≅ snd x
  e2' {x} = 
    let h = H.≡-subst-removable (λ x₁ → val (B x₁)) (bwd-fwd (rep cA) (fst x))
            (bwd (rep (cB (bwd (rep cA) (fwd (rep cA) (fst x)))))
            (P.subst (λ a → Carrier (cB a)) (symm (bwd-fwd (rep cA) (fst x)))
              (fwd (rep (cB (fst x))) (snd x)))) in 
    let h1 = H.≡-subst-removable (λ a → Carrier (cB a)) (symm (bwd-fwd (rep cA) (fst x)))
              (fwd (rep (cB (fst x))) (snd x)) in 
    let h2 = H.icong (λ i → Carrier (cB i)) (bwd-fwd (rep cA) (fst x)) (λ {k} z → bwd (rep (cB k)) z) h1 in
    let h3 = H.≡-to-≅ (bwd-fwd (rep (cB (fst x))) (snd x)) in 
    H.trans h (H.trans h2 h3) 

  e2 : ∀ {x} → P.subst (λ x₁ → val (B x₁)) (bwd-fwd (rep cA) (fst x))
    (bwd (rep (cB (bwd (rep cA) (fwd (rep cA) (fst x)))))
     (P.subst (λ a → Carrier (cB a)) (symm (bwd-fwd (rep cA) (fst x)))
      (fwd (rep (cB (fst x))) (snd x))))
    ≡ snd x 
  e2 = H.≅-to-≡ e2'
  
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

e/meta : ∀ {A} → Ext (U (meta A)) 
e/meta {A} = record {
    Carrier = A
  ; rep = record { 
      fwd = id 
    ; bwd = id 
    ; fwd-bwd = λ _ → refl
    ; bwd-fwd = λ _ → refl
    }
  }

-- fun : 
--   (A : tp pos) →
--   (h : Ext A) →
--   (B : val A → tp pos) →
--   (p : Ext.𝒜 h → ℕ) → 
--   (body : (a : val A) → 
--           (self : cmp (Σ++ A λ a' → meta (lt/cost h p a' a) ⇒ (λ s → B (s . fst)) [ h ,  ] ) )