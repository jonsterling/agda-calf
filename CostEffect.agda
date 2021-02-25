{-# OPTIONS --prop --rewriting #-}

module CostEffect where

open import Prelude
open import CBPV

postulate
  ext : Ω
  step : ∀ X → cmp X → cmp X
  step/ext : ∀ {X} → (e : cmp X) → ext → step X e ≡ e
  -- sadly the above cannot be made an Agda rewrite rule

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} → step (Π A X) f ≡ λ x → step (X x) (f x)
  {-# REWRITE Π/step #-}

  Σ+-/step : ∀ {A} {X : val A → tp neg} {p : cmp (Σ+- A X)} → step (Σ+- A X) p ≡ (fst p , step (X (fst p)) (snd p))
  {-# REWRITE Σ+-/step #-}

  -- I think this is the law that we want to forget costs when constructing elements of a computation type
  U_step : ∀ {A} {X : val A → tp neg} {e} → U (tbind (step (F A) e) X) ≡ U (tbind e X)
  {-# REWRITE U_step #-}

  bind/step : ∀ {A} {X} {e f} → bind X (step (F A) e) f ≡ step X (bind X e f)
  dbind/step : ∀ {A} {X : val A → tp neg} {e f} → dbind X (step (F A) e) f ≡ step (tbind e X) (dbind X e f)
  {-# REWRITE bind/step dbind/step #-}


-- I am a little less scared of this version.
postulate
  ► : tp pos → tp pos
  ►/ret : ∀ A → val A → val (► A)
  ►/match : ∀ {A} X → val (► A) → (val A → cmp X) → cmp X
  ►/match/ret : ∀ {A X} {u : val A} {f : val A → cmp X} → ►/match X (►/ret A u) f ≡ step X (f u)
  {-# REWRITE ►/match/ret #-}

  ►/ext : ∀ A → ext → val (► A) → val A
  ►/ext/β : ∀ {A} {z : ext} {u : val A} → ►/ext A z (►/ret A u) ≡ u
  {-# REWRITE ►/ext/β #-}

  ►/ext/η : ∀ {A} (z : ext) (u : val (► A)) → ►/ret A (►/ext A z u) ≡ u

►/ext/match : ∀ {A X} {u : val (► A)} {f : val A → cmp X} {z : ext} → ►/match X u f ≡ f (►/ext A z u)
►/ext/match {A} {X} {u} {f} {z} rewrite (symm (►/ext/η z u)) = step/ext {X} (f (►/ext A z u)) z

-- I don't know the above is strong enough, but at least it seems not
-- too strong lol.  The thing I am struggling with is, I basically
-- want some kind of abstract type in the LF that forces you to take a
-- step, but I don't want you to be able to extract the thing that
-- takes that step internally. That's why this is not really the same
-- as the refinement that you get by looking at the image of "step".
postulate
  ▷ : tp neg → tp neg
  ▷/ret : ∀ X → cmp X → cmp (▷ X)
  ▷/match : ∀ {X} Y → cmp (▷ X) → (cmp X → cmp Y) → cmp Y
  ▷/match/ret : ∀ {X Y} {e : cmp X} {f : cmp X → cmp Y} → ▷/match Y (▷/ret X e) f ≡ step Y (f e)
  {-# REWRITE ▷/match/ret #-}

  ▷/ext : ∀ X → ext → cmp (▷ X) → cmp X
  ▷/ext/β : ∀ {X} {z : ext} {u : cmp X} → ▷/ext X z (▷/ret X u) ≡ u
  {-# REWRITE ▷/ext/β #-}

  ▷/ext/η : ∀ {X} (z : ext) (u : cmp (▷ X)) → ▷/ret X (▷/ext X z u) ≡ u

▷/ext/match : ∀ {Y X} {u : cmp (▷ Y)} {f : cmp Y → cmp X} {z : ext} → ▷/match X u f ≡ f (▷/ext Y z u)
▷/ext/match {Y} {X} {u} {f} {z} rewrite (symm (▷/ext/η z u)) = step/ext {X} (f (▷/ext Y z u)) z
