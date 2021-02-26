{-# OPTIONS --prop --rewriting #-}

-- The is the basic CBPV metalanguage.

module Metalanguage where

open import Prelude

postulate
  mode : □
  pos : mode
  neg : mode

  tp : mode → □
  val : tp pos → □

  F : tp pos → tp neg
  U : tp neg → tp pos

-- This is equivalent to adding "thunk / force" operations. But less bureaucratic.
cmp : tp neg → □
cmp X = val (U X)

postulate
  ret : ∀ {A} → val A → cmp (F A)
  tbind : ∀ {A} → cmp (F A) → (val A → tp neg) → tp neg
  tbind_ret : ∀ {A} {X : val A → tp neg} {v : val A} → tbind (ret v) X ≡ X v
  {-# REWRITE tbind_ret #-}

  dbind : ∀ {A} (X : val A → tp neg) (e : cmp (F A)) (f : (x : val A) → cmp (X x)) → cmp (tbind e X)

  -- note that bind is not a special case of dbind: in general, one does not expect (tbind e (λ _ → m)) ≡ m.
  -- This would hold, however, in the case of a language where there are no true effects. But we don't want
  -- to assume that.
  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X

  bind/ret : ∀ {A X} {v : val A} {f : (x : val A) → cmp X} → bind X (ret v) f ≡ f v
  dbind/ret : ∀ {A} {X : val A → tp neg} {v : val A} {f : (x : val A) → cmp (X x)} → dbind X (ret v) f ≡ f v
  {-# REWRITE bind/ret dbind/ret #-}

  tbind/assoc : ∀ {A B X} {e : cmp (F A)} {f : val A → cmp (F B)} → 
    tbind {B} (bind (F B) e f) X ≡ tbind {A} e (λ v → tbind {B} (f v) X)
  {-# REWRITE tbind/assoc #-}
  -- todo: add bind/assoc
  -- todo: add dbind/assoc

  -- dependent product
  Π : (A : tp pos) (X : val A → tp neg) → tp neg
  Π/decode : ∀ {A} {X : val A → tp neg} → val (U (Π A X)) ≡ ((x : val A) → cmp (X x))
  {-# REWRITE Π/decode #-}

  -- mixed polarity dependent sum
  Σ+- : (A : tp pos) (X : val A → tp neg) → tp neg
  Σ+-/decode : ∀ {A} {X : val A → tp neg} → val (U (Σ+- A X)) ≡ Σ (val A) λ x → cmp (X x)
  {-# REWRITE Σ+-/decode #-}

  -- positive dependent sum
  Σ++ : (A : tp pos) (B : val A → tp pos) → tp pos
  Σ++/decode : ∀ {A} {B : val A → tp pos} → val (Σ++ A B) ≡ Σ (val A) λ x → val (B x)
  {-# REWRITE Σ++/decode #-}
