{-# OPTIONS --cubical-compatible --lossy-unification --rewriting #-}

module CalfNew.Metalanguage where

open import CalfNew.Prelude

module Imp where
  postulate
    M : Set → Set
    M/ret : ∀ {A} → A → M A
    M/bind : ∀ {A B} → M A → (A → M B) → M B

    M/bind-ret : ∀ {A B} a f → M/bind {A} {B} (M/ret a) f ≡ f a
    M/bind-bind : ∀ {A B C} e f g → M/bind {B} {C} (M/bind {A} e f) g ≡ M/bind e λ a → M/bind (f a) g

  data tp+ : Set₁
  data tp- : Set₁

  val : tp+ → Set
  cmp : tp- → Set

  data tp+ where
    U : tp- → tp+
    meta : Set → tp+

  data tp- where
    F : tp+ → tp-
    Π : ∀ A → (val A → tp-) → tp-

  val (U X) = cmp X
  val (meta A) = A

  cmp (F A) = M (val A)
  cmp (Π A X) = ∀ a → cmp (X a)

  ret : ∀ {A} → val A → cmp (F A)
  ret = M/ret

  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X
  bind (F B) = M/bind
  bind (Π B X) e f b = bind (X b) e λ a → f a b

  bind-ret : ∀ {A} X a f → bind {A} X (ret a) f ≡ f a
  bind-ret (F B) = M/bind-ret
  bind-ret (Π B X) a f = funext λ b → bind-ret (X b) a λ a → f a b

  bind-bind : ∀ {A B} X e f₁ f₂ → bind X (bind {A} (F B) e f₁) f₂ ≡ bind X e λ a → bind X (f₁ a) f₂
  bind-bind (F C) = M/bind-bind
  bind-bind (Π C X) e f₁ f₂ = funext λ c → bind-bind (X c) e f₁ λ b → f₂ b c

opaque
  tp+ : Set₁
  tp+ = Imp.tp+

  tp- : Set₁
  tp- = Imp.tp-

  val : tp+ → Set
  val = Imp.val

  cmp : tp- → Set
  cmp = Imp.cmp

  U : tp- → tp+
  U = Imp.U

  meta : Set → tp+
  meta = Imp.meta

  F : tp+ → tp-
  F = Imp.F

  Π : ∀ A → (val A → tp-) → tp-
  Π = Imp.Π

  ret : ∀ {A} → val A → cmp (F A)
  ret = Imp.ret

  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X
  bind = Imp.bind

  private
    val-U : ∀ {X} → val (U X) ≡ cmp X
    val-U = refl
    {-# REWRITE val-U #-}

    val-meta : ∀ {A} → val (meta A) ≡ A
    val-meta = refl
    {-# REWRITE val-meta #-}

    cmp-Π : ∀ {A X} → cmp (Π A X) ≡ ∀ a → cmp (X a)
    cmp-Π = refl
    {-# REWRITE cmp-Π #-}

    bind-Π : ∀ {A B X e f} → bind {A} (Π B X) e f ≡ λ b → bind (X b) e λ a → f a b
    bind-Π = refl
    {-# REWRITE bind-Π #-}

    bind-ret : ∀ {A} X a f → bind {A} X (ret a) f ≡ f a
    bind-ret = Imp.bind-ret
    {-# REWRITE bind-ret #-}

    bind-bind : ∀ {A B} X e f₁ f₂ → bind X (bind {A} (F B) e f₁) f₂ ≡ bind X e λ a → bind X (f₁ a) f₂
    bind-bind = Imp.bind-bind
    {-# REWRITE bind-bind #-}

infixr 3 Π
syntax Π A (λ _ → X) = A ⇒ X
