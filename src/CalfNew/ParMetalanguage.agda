{-# OPTIONS --cubical-compatible --lossy-unification --rewriting #-}

open import CalfNew.CostMonoid

module CalfNew.ParMetalanguage (parCostMonoid : ParCostMonoid) where

open ParCostMonoid parCostMonoid

open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality.Core

open import CalfNew.Prelude
import CalfNew.Metalanguage as Metalanguage
import CalfNew.Step costMonoid as Step

module Imp where
  open Metalanguage.Imp
  open Step.Imp

  infixr 7 _M/&_ _&_

  postulate
    _M/&_ : ∀ {A B} → M A → M B → M (Σ A λ _ → B)

    M/step-ret-&-step-ret : ∀ {A B} p q a b → M/step {A} p (M/ret a) M/& M/step {B} q (M/ret b) ≡ M/step (p ⊗ q) (M/ret (a , b))

  _&_ : ∀ {A B} → cmp (F A) → cmp (F B) → cmp (F (meta _))
  _&_ = _M/&_

  step-ret-&-step-ret : ∀ {A B} p q a b → step (F A) p (ret a) & step (F B) q (ret b) ≡ step (F _) (p ⊗ q) (ret (a , b))
  step-ret-&-step-ret = M/step-ret-&-step-ret

  step-ret-&-ret : ∀ {A B} p a b → step (F A) p (ret a) & ret {B} b ≡ step (F _) (p ⊗ 𝟘) (ret (a , b))
  step-ret-&-ret p a b = trans (cong (_ &_) (sym (step-𝟘 _ _))) (step-ret-&-step-ret p 𝟘 a b)

  ret-&-step-ret : ∀ {A B} q a b → ret {A} a & step (F B) q (ret b) ≡ step (F _) (𝟘 ⊗ q) (ret (a , b))
  ret-&-step-ret q a b = trans (cong (_& _) (sym (step-𝟘 _ _))) (step-ret-&-step-ret 𝟘 q a b)

  ret-&-ret : ∀ {A B} a b → ret {A} a & ret {B} b ≡ step (F _) (𝟘 ⊗ 𝟘) (ret (a , b))
  ret-&-ret a b = trans (cong (_& _) (sym (step-𝟘 _ _))) (step-ret-&-ret 𝟘 a b)

open Metalanguage
open Step
open import CalfNew.Types.Sigma

opaque
  unfolding cmp step

  infixr 7 _&_

  _&_ : ∀ {A B} → cmp (F A) → cmp (F B) → cmp (F (A ×′ B))
  _&_ = Imp._&_

  private
    step-ret-&-step-ret : ∀ {A B} p q a b → step (F A) p (ret a) & step (F B) q (ret b) ≡ step (F (A ×′ B)) (p ⊗ q) (ret (a , b))
    step-ret-&-step-ret = Imp.step-ret-&-step-ret
    {-# REWRITE step-ret-&-step-ret #-}

    step-ret-&-ret : ∀ {A B} p a b → step (F A) p (ret a) & ret {B} b ≡ step (F (A ×′ B)) (p ⊗ 𝟘) (ret (a , b))
    step-ret-&-ret = Imp.step-ret-&-ret
    {-# REWRITE step-ret-&-ret #-}

    ret-&-step-ret : ∀ {A B} q a b → ret a & step (F B) q (ret b) ≡ step (F (A ×′ B)) (𝟘 ⊗ q) (ret (a , b))
    ret-&-step-ret = Imp.ret-&-step-ret
    {-# REWRITE ret-&-step-ret #-}

    ret-&-ret : ∀ {A B} a b → ret a & ret b ≡ step (F (A ×′ B)) (𝟘 ⊗ 𝟘) (ret (a , b))
    ret-&-ret = Imp.ret-&-ret
    {-# REWRITE ret-&-ret #-}
