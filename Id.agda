{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Cost
open import Upper
open import Eq
open import Data.Nat as Nat
open import Connectives renaming (_⇒_[_,_] to Ψ)
open import Function
open import Relation.Binary.PropositionalEquality as P
open import Num
open import Induction.WellFounded
open import Induction
open import Data.Nat.Properties
open import Refinement

id/cost : ℕ → ℕ 
id/cost n = n

baz : (y : val num) → if {λ _ → ℕ} (to-nat y) 0 (λ n → suc n) ≡ to-nat y 
baz y with to-nat y 
... | zero = refl
... | suc n = refl

num-suc : cmp (F num) → cmp (F num)
num-suc c = bind {num} (F num) c λ n → ret {num} (to-num (suc (to-nat n)))

id/hard/body : (y : val num) → 
        WfRec (lt/cost e/num id/cost) (λ x → cmp (F num)) y → 
        cmp (F num)
id/hard/body y h = ifz (λ _ → F num) y 
            (ret {num} (to-num 0)) 
            (λ y' h' → step' (F num) 1 (num-suc (h y' (≤-≡ h'))))

id/hard/code : cmp (num ⇒ F num)
id/hard/code = λ x → All.wfRec (lt/cost/wf {num} {e/num} {id/cost}) _ 
    (λ _ → cmp (F num)) 
    id/hard/body 
    x

body-ext : (x : val num) → 
      {IH IH' : WfRec (lt/cost e/num id/cost) (λ x → cmp (F num)) x} → 
      (∀ {y} y<x → IH y y<x ≡ IH' y y<x) → 
      id/hard/body x IH ≡ id/hard/body x IH' 
body-ext x h = P.cong (λ f → ifz (λ _ → F num) x (ret {num} (to-num 0)) f) 
                   (funext λ y' → funext λ h' →  
                    P.cong (step' (F num) 1 ∘ num-suc) (h (≤-≡ h')))
    
id/hard : cmp (Ψ num (λ _ → num) e/num id/cost)
id/hard = 
  id/hard/code , e

  where 
  func = id/hard/code
  body = id/hard/body

  e : ∀ x → cmp (ub⁻ num (func x) (id/cost (to-nat x)))
  e x = iso.fwd ub⁻/decode 
          (All.wfRec (lt/cost/wf {num} {e/num} {id/cost}) _ 
            (λ x → ub num (func x) (to-nat x))
            (λ y h → foo {y} h) x)
    where 
    bar : ∀ {y : val num} → 
      WfRec (lt/cost e/num id/cost) (λ x → ub num (func x) (to-nat x)) y → 
      ub num (func y) (if {λ _ → ℕ} (to-nat y) 0 (λ n → suc n))
    bar {y} h1 rewrite FixPoint.unfold-wfRec 
        (lt/cost/wf {num} {e/num} {id/cost}) 
        (λ _ → cmp (F num))
        body 
        body-ext {y} = 
          ub/ifz (λ _ → num) y (ret {num} (to-num 0)) 
          (λ y' h' → step' (F num) 1 (num-suc (func y'))) 
          0 suc (ub/ret 0) 
          (λ y' h → 
          P.subst (λ n → ub num (step' (F num) 1 (num-suc (func y'))) n) 
          (P.trans (+-suc (to-nat y') zero) (P.cong suc (+-identityʳ (to-nat y'))))
          (ub/step (to-nat y') 1 
          (P.subst (λ n → ub num (num-suc (func y')) n)
            (+-identityʳ (to-nat y'))
            (ub/bind/const e/num (to-nat y') 0 (h1 y' (≤-≡ h)) (λ _ → ub/ret 0))
          )
          )
          )

    foo : ∀ {y} → 
      WfRec (lt/cost e/num id/cost) (λ x → ub num (func x) (to-nat x)) y → 
      ub num (func y) (to-nat y) 
    foo {y} h = P.subst (λ n → ub num (func y) n) (baz y) (bar {y} h)

id/easy/code : cmp (num ⇒ F num)
id/easy/code = λ x → ret {num} x

id/easy : cmp (Ψ num (λ _ → num) e/num (const 0)) 
id/easy = id/easy/code , 
          λ x → iso.fwd ub⁻/decode 
            (ub/ret 0)

open Some 
id/hard≡id/easy : ◯ (∀ x → id/hard/code x ≡ id/easy/code x)
id/hard≡id/easy u x = 
  All.wfRec (lt/cost/wf {num} {e/num} {id/cost}) _ 
  (λ x → id/hard/code x ≡ id/easy/code x) 
  (λ y h → 
    ifz
    (λ n → meta (id/hard/code (to-num n) ≡ id/easy/code (to-num n))) 
    y
    refl 
    λ y' h' → foo y h y' h') x 
  where 
  foo : (y : val num) → ((y' : val num) →  (lt/cost e/num id/cost) y' y → id/hard/code y' ≡ id/easy/code y') → 
        (y' : val num) → 
        (h' : suc (to-nat y') ≡ to-nat y) → 
        id/hard/code (to-num (suc (to-nat y'))) ≡ id/easy/code (to-num (suc (to-nat y'))) 
  foo y h y' h' rewrite FixPoint.unfold-wfRec 
        (lt/cost/wf {num} {e/num} {id/cost}) 
        (λ _ → cmp (F num))
        id/hard/body 
        body-ext {to-num (suc (to-nat y'))} = 
        let g = P.cong ((step' (F num) 1) ∘ num-suc) (h y' (≤-≡ h')) in
        P.trans g (step'/ext (F num) (ret {num} (to-num (suc (to-nat y')))) 1 u)