{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Monad where

open Agda.Primitive
open import Agda.Builtin.Equality

record Monad {ℓ ℓ′} (M : Set ℓ → Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′) where
  infix 5 _>>=_ _>>_ _<*>_

  field
    pure : ∀ {A} → A → M A
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B

    pure->>= : ∀ {A B} a (f : A → M B) → pure a >>= f ≡ f a
    >>=-pure : ∀ {A} x → x >>= pure {A} ≡ x
    >>=->>= : ∀ {A B C} x f (g : B → M C) → (x >>= f) >>= g ≡ x >>= λ (a : A) → f a >>= g

  _>>_ : ∀ {A B} → M A → M B → M B
  x >> y = x >>= λ _ → y

  _<*>_ : ∀ {A B} → M (A → B) → M A → M B
  x <*> y = x >>= λ f → y >>= λ a → pure (f a)

record MonadLift {ℓ ℓ′ ℓ″ ℓ‴} (M : Set ℓ → Set ℓ′) (M′ : Set ℓ″ → Set ℓ‴) : Set (lsuc ℓ ⊔ ℓ′ ⊔ lsuc ℓ″ ⊔ ℓ‴) where
  field
    lift : ∀ {A B} → M A → (A → M′ B) → M′ B
