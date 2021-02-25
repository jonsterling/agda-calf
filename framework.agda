{-# OPTIONS --prop --rewriting #-}

module framework where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Sigma

Ω = Prop
□ = Set

data image (A B : □) (f : A → B) : B → Ω where
  image/in : (x : A) → image A B f (f x)

record sub (A : □) (ϕ : A → Ω) : □ where
  constructor sub/in
  field
    sub/wit : A
    sub/prf : ϕ sub/wit

open sub public

symm : {A : □} {a b : A} → a ≡ b → b ≡ a
symm refl = refl

postulate
  ext : Ω
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
  -- This would hold, however, in the case of a language where the only effect is stepping. But we don't want
  -- to assume that.
  bind : ∀ {A} X → cmp (F A) → (val A → cmp X) → cmp X

  bind/ret : ∀ {A X} {v : val A} {f : (x : val A) → cmp X} → bind X (ret v) f ≡ f v
  dbind/ret : ∀ {A} {X : val A → tp neg} {v : val A} {f : (x : val A) → cmp (X x)} → dbind X (ret v) f ≡ f v
  {-# REWRITE bind/ret dbind/ret #-}

  -- todo: add bind/assoc
  -- todo: add dbind/assoc


postulate
  step : ∀ X → cmp X → cmp X
  step/ext : ∀ {X} → (e : cmp X) → ext → step X e ≡ e
  -- sadly the above cannot be made an Agda rewrite rule

postulate
  -- I think this is the law that we want to forget costs when constructing elements of a computation type
  U_step : ∀ {A} {X : val A → tp neg} {e} → U (tbind (step (F A) e) X) ≡ U (tbind e X)
  {-# REWRITE U_step #-}

  bind/step : ∀ {A} {X} {e f} → bind X (step (F A) e) f ≡ step X (bind X e f)
  dbind/step : ∀ {A} {X : val A → tp neg} {e f} → dbind X (step (F A) e) f ≡ step (tbind e X) (dbind X e f)
  {-# REWRITE bind/step dbind/step #-}

postulate

  -- cost-insensitive dependent product
  Π : (A : tp pos) (X : val A → tp neg) → tp neg
  Π/decode : ∀ {A} {X : val A → tp neg} → val (U (Π A X)) ≡ ((x : val A) → cmp (X x))
  {-# REWRITE Π/decode #-}

  Π/step : ∀ {A} {X : val A → tp neg} {f : cmp (Π A X)} → step (Π A X) f ≡ λ x → step (X x) (f x)
  {-# REWRITE Π/step #-}

  -- cost-insensitive mixed polarity dependent sum
  Σ+- : (A : tp pos) (X : val A → tp neg) → tp neg
  Σ+-/decode : ∀ {A} {X : val A → tp neg} → val (U (Σ+- A X)) ≡ Σ (val A) λ x → cmp (X x)
  {-# REWRITE Σ+-/decode #-}

  Σ+-/step : ∀ {A} {X : val A → tp neg} {p : cmp (Σ+- A X)} → step (Σ+- A X) p ≡ (fst p , step (X (fst p)) (snd p))
  {-# REWRITE Σ+-/step #-}

  -- cost-insensitive positive dependent sum
  Σ++ : (A : tp pos) (B : val A → tp pos) → tp pos
  Σ++/decode : ∀ {A} {B : val A → tp pos} → val (Σ++ A B) ≡ Σ (val A) λ x → val (B x)
  {-# REWRITE Σ++/decode #-}


-- I am a little less scared of this version.
-- TODO: make the following operations be the identity underneath 'ext'.
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

postulate
  bool : tp pos
  tt ff : val bool

boolc : tp pos
boolc = ► bool


-- This version of the dependent product costs a step to apply.
-- One thing I noticed is that this version may not quite capture what I had in mind trying to force
-- the application to take a step.
Πc : (A : tp pos) (X : val A → tp neg) → tp neg
Πc A X = Π A λ x → ▷ (X x)
