{-# OPTIONS --prop --without-K --rewriting #-}

-- This module extends the CBPV metalanguage with effects corresponding to computational steps.

open import Calf.CostMonoid

module Calf.CostEffect where

open import Calf.Prelude
open import Calf.Metalanguage
open import Data.Product

postulate
  step : ∀ X → cmp X → cmp X

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} → step (Π A X) f ≡ λ x → step (X x) (f x)
  {-# REWRITE Π/step #-}

  Σ+-/step : ∀ {A} {X : val A → tp neg} {p : cmp (Σ+- A X)} → step (Σ+- A X) p ≡ (proj₁ p , step (X (proj₁ p)) (proj₂ p))
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
