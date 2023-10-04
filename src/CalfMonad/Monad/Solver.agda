{-# OPTIONS --erased-cubical --safe #-}

module CalfMonad.Monad.Solver where

open Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Function.Base                              using (_$_; _∘_)
open import Reflection.Argument                        using (_⟅∷⟆_; _⟨∷⟩_; vArg)
open import Reflection.Term                            using (vLam)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans)

open import CalfMonad.Monad
open import CalfMonad.Prelude

module MonadSolver {ℓ ℓ′ M} monad where
  open Monad {ℓ} {ℓ′} {M} monad

  private
    data Expr : Set ℓ → Set (lsuc ℓ ⊔ ℓ′) where
      _↑ : ∀ {A} → M A → Expr A
      pure′ : ∀ {A} → A → Expr A
      _>>=′_ : ∀ {A B} → Expr A → (A → Expr B) → Expr B

    _↓ : ∀ {A} → Expr A → M A
    x ↑ ↓ = x
    pure′ a ↓ = pure a
    (x >>=′ f) ↓ = x ↓ >>= λ a → f a ↓

    _⇓>>=_ : ∀ {A B} → Expr A → (A → M B) → M B
    (x ↑) ⇓>>= f = x >>= f
    pure′ a ⇓>>= f = f a
    (x >>=′ f) ⇓>>= g = x ⇓>>= λ a → f a ⇓>>= g

    _⇓ : ∀ {A} → Expr A → M A
    x ⇓ = x ⇓>>= pure

    sound>>= : ∀ {A B} x (f : A → M B) → x ⇓>>= f ≡ x ↓ >>= f
    sound>>= (x ↑) f = refl
    sound>>= (pure′ a) f rewrite pure->>= a f = refl
    sound>>= (x >>=′ f) g rewrite sound>>= x λ a → f a ⇓>>= g rewrite funext λ a → sound>>= (f a) g rewrite >>=->>= (x ↓) (λ a → f a ↓) g = refl

    sound : ∀ {A} (x : Expr A) → x ⇓ ≡ x ↓
    sound x rewrite sound>>= x pure = >>=-pure (x ↓)

    parseExpr : Term → TC Term
    parseExpr (def (quote Monad.pure) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟨∷⟩ A ⟅∷⟆ a ⟨∷⟩ [])) =
      returnTC (con (quote pure′) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟅∷⟆ A ⟅∷⟆ a ⟨∷⟩ []))
    parseExpr (def (quote Monad._>>=_) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟨∷⟩ A ⟅∷⟆ B ⟅∷⟆ x ⟨∷⟩ f ⟨∷⟩ [])) =
      bindTC (parseExpr x) λ x →
      bindTC (parseExprFun f) λ f →
      returnTC (con (quote _>>=′_) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟅∷⟆ A ⟅∷⟆ B ⟅∷⟆ x ⟨∷⟩ f ⟨∷⟩ []))
      where
        parseExprFun : Term → TC Term
        parseExprFun (vLam a f) =
          bindTC (extendContext a (vArg A) (parseExpr f)) λ f →
          returnTC (vLam a f)
        parseExprFun (def (quote Monad.pure) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟨∷⟩ A ⟅∷⟆ [])) =
          returnTC (con (quote pure′) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟅∷⟆ A ⟅∷⟆ []))
        parseExprFun f =
          returnTC (def (quote _∘_) (con (quote _↑) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟅∷⟆ B ⟅∷⟆ []) ⟨∷⟩ f ⟨∷⟩ []))
    parseExpr x =
      bindTC (quoteTC ℓ) λ ℓ →
      bindTC (quoteTC ℓ′) λ ℓ′ →
      bindTC (quoteTC M) λ M →
      bindTC (quoteTC monad) λ monad →
      returnTC (con (quote _↑) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟅∷⟆ unknown ⟅∷⟆ x ⟨∷⟩ []))

  macro
    solve : Term → TC _
    solve hole = bindTC (inferType hole) λ where
      (def (quote _≡_) (_ ⟅∷⟆ _ ⟅∷⟆ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) →
        bindTC (parseExpr lhs) λ lhs →
        bindTC (parseExpr rhs) λ rhs →
        bindTC (quoteTC ℓ) λ ℓ →
        bindTC (quoteTC ℓ′) λ ℓ′ →
        bindTC (quoteTC M) λ M →
        bindTC (quoteTC monad) λ monad →
        unify hole (def (quote trans) (def (quote sym) (def (quote sound) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟨∷⟩ unknown ⟅∷⟆ lhs ⟨∷⟩ []) ⟨∷⟩ []) ⟨∷⟩ def (quote sound) (ℓ ⟅∷⟆ ℓ′ ⟅∷⟆ M ⟅∷⟆ monad ⟨∷⟩ unknown ⟅∷⟆ rhs ⟨∷⟩ []) ⟨∷⟩ []))
      (meta x _) → blockOnMeta x
      ty → typeError (strErr "expected equality, got " ∷ termErr ty ∷ [])

{-
module _ {ℓ M} monad where
  open Monad {ℓ} {ℓ} {M} monad
  open MonadSolver monad

  foo : ∀ {A} (a : A) → pure (pure a) >>= (λ x → x) ≡ pure a
  foo {A} a = {!!}
-}
