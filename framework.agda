{-# OPTIONS --prop --rewriting #-}

module framework where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public


Ω = Prop
□ = Set

postulate
  ext : Ω
  mode : □
  pos : mode
  neg : mode

  tp : mode → □
  val : tp pos → □

  F : tp pos → tp neg
  U : tp neg → tp pos

cmp : tp neg → □
cmp X = val (U X)

postulate
  ret : ∀ {A} → val A → cmp (F A)
  tbind : ∀ {A} → cmp (F A) → (val A → tp neg) → tp neg
  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X
  dbind : ∀ {A} (X[_] : val A → tp neg) (e : cmp (F A)) (f : (x : val A) → cmp X[ x ]) → cmp (tbind e X[_])

  bind_ret : ∀ {A X} {v : val A} {f : (x : val A) → cmp X} → bind X (ret v) f ≡ f v
  {-# REWRITE bind_ret #-}

postulate
  step : ∀ X → cmp X → cmp X
  step_ext : ∀ {X} → (e : cmp X) → ext → step X e ≡ e


postulate
  U_step : ∀ {A} {X[_] : val A → tp neg} {e} → U (tbind (step (F A) e) X[_]) ≡ U (tbind e X[_])
  {-# REWRITE U_step #-}

  step_bind : ∀ {A} {X} {e f} → bind X (step (F A) e) f ≡ step X (bind X e f)
  {-# REWRITE step_bind #-}

  step_dbind : ∀ {A} {X[_] : val A → tp neg} {e f} → dbind X[_] (step (F A) e) f ≡ step (tbind e X[_]) (dbind X[_] e f)
  {-# REWRITE step_dbind #-}


postulate
  ▷ : tp neg → tp neg
  ▷/inv : ∀ {X} → cmp X → cmp (▷ X)
  ▷/dir : ∀ {X} → cmp (▷ X) → cmp X
  ▷/beta : ∀ {X} {e : cmp X} → ▷/dir {X} (▷/inv e) ≡ step X e
  ▷/step : ∀ {X} {e : cmp (▷ X)} → step (▷ X) e ≡ ▷/inv (▷/dir e)
  {-# REWRITE ▷/beta ▷/step #-}

  Π : (A : tp pos) (X[_] : val A → tp neg) → tp neg
  Π/cmp : ∀ {A} {X[_] : val A → tp neg} → val (U (Π A X[_])) ≡ ((x : val A) → cmp X[ x ])
  {-# REWRITE Π/cmp #-}
