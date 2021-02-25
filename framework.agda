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
  tbind_ret : ∀ {A} {X : val A → tp neg} {v : val A} → tbind (ret v) X ≡ X v
  {-# REWRITE tbind_ret #-}

  dbind : ∀ {A} (X[_] : val A → tp neg) (e : cmp (F A)) (f : (x : val A) → cmp X[ x ]) → cmp (tbind e X[_])

  -- note that bind is not a special case of dbind: in general, one does not expect (tbind e (λ _ → m)) ≡ m.
  -- This would hold, however, in the case of a language where the only effect is stepping. But we don't want
  -- to assume that.
  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X

  bind_ret : ∀ {A X} {v : val A} {f : (x : val A) → cmp X} → bind X (ret v) f ≡ f v
  {-# REWRITE bind_ret #-}

  -- todo: add dbind_ret
  -- todo: add bind_assoc
  -- todo: add dbind_assoc

postulate
  step : ∀ X → cmp X → cmp X
  step_ext : ∀ {X} → (e : cmp X) → ext → step X e ≡ e


postulate
  -- I think this is the law that we want to forget costs when constructing elements of a computation type
  U_step : ∀ {A} {X : val A → tp neg} {e} → U (tbind (step (F A) e) X) ≡ U (tbind e X)
  {-# REWRITE U_step #-}

  step_dbind : ∀ {A} {X : val A → tp neg} {e f} → dbind X (step (F A) e) f ≡ step (tbind e X) (dbind X e f)
  {-# REWRITE step_dbind #-}

  step_bind : ∀ {A} {X} {e f} → bind X (step (F A) e) f ≡ step X (bind X e f)
  {-# REWRITE step_bind #-}


postulate
  -- the primitive "at least one step" refinement
  ▷ : tp neg → tp neg
  ▷/inv : ∀ {X} → cmp X → cmp (▷ X)
  ▷/dir : ∀ {X} → cmp (▷ X) → cmp X
  ▷/beta : ∀ {X} {e : cmp X} → ▷/dir {X} (▷/inv e) ≡ step X e
  ▷/step : ∀ {X} {e : cmp (▷ X)} → step (▷ X) e ≡ ▷/inv (▷/dir e)
  {-# REWRITE ▷/beta ▷/step #-}

  -- cost-insensitive dependent product
  Π : (A : tp pos) (X : val A → tp neg) → tp neg
  Π/cmp : ∀ {A} {X : val A → tp neg} → val (U (Π A X)) ≡ ((x : val A) → cmp (X x))
  {-# REWRITE Π/cmp #-}

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} → step (Π A X) f ≡ λ x → step (X x) (f x)
  {-# REWRITE Π/step #-}

-- This version of the dependent product costs a step to apply.
Πc : (A : tp pos) (X : val A → tp neg) → tp neg
Πc A X = Π A λ x → ▷ (X x)
