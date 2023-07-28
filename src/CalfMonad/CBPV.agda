{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

module CalfMonad.CBPV {ℓ ℓ′} {M : Set ℓ → Set ℓ′} (monad : Monad M) where

open Monad monad

open Agda.Primitive
open import Agda.Builtin.List
open import Axiom.Extensionality.Propositional         using (Extensionality)
open import Data.List.Relation.Unary.All               using (All; []; _∷_; map)
open import Function.Base                              using (id)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_)

tp+ : Set (lsuc ℓ)
tp+ = Set ℓ

record tp- : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    U : Set ℓ′
    bind : {A : tp+} → M A → (A → U) → U

    pure-bind : Extensionality ℓ ℓ′ → ∀ {A} a f → bind {A} (pure a) f ≡ f a
    >>=-bind : Extensionality ℓ ℓ′ → ∀ {A B} e f g → bind {B} (e >>= f) g ≡ bind {A} e λ a → bind (f a) g

open tp- public

F : tp+ → tp-
U (F A) = M A
bind (F B) = _>>=_
pure-bind (F B) ext = pure->>=
>>=-bind (F C) ext = >>=->>=

seqbind : ∀ X {As : List tp+} → All M As → (All id As → U X) → U X
seqbind X [] f = f []
seqbind X (e ∷ es) f = bind X e λ a → seqbind X es λ as → f (a ∷ as)

open ≡-Reasoning

pure-seqbind : ∀ X → Extensionality ℓ ℓ′ → ∀ {As} as f → seqbind X {As} (map pure as) f ≡ f as
pure-seqbind X ext [] f = begin
  f [] ∎
pure-seqbind X ext (a ∷ as) f = begin
  bind X (pure a) (λ a → seqbind X (map pure as) λ as → f (a ∷ as)) ≡⟨ pure-bind X ext a _ ⟩
  seqbind X (map pure as) (λ as → f (a ∷ as))                       ≡⟨ pure-seqbind X ext as _ ⟩
  f (a ∷ as)                                                        ∎
