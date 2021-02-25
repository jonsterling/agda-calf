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


postulate
  ▷ : (X : tp neg) → tp neg
  ▷/decode : ∀ {X} → val (U (▷ X)) ≡ sub (cmp X) (image _ _ (step X))
  {-# REWRITE ▷/decode #-}

▷/dir : (X : tp neg) → cmp (▷ X) → cmp X
▷/dir X x = sub/wit x

▷/inv : (X : tp neg) → cmp X → cmp (▷ X)
sub/wit (▷/inv X x) = step X x
sub/prf (▷/inv X x) = image/in x

postulate
  ▷/step : ∀ {X} (x : cmp (▷ X)) → step (▷ X) x ≡ ▷/inv X (▷/dir X x)
  {-# REWRITE ▷/step #-}

▷/beta : ∀ {X} {x : cmp X} → ▷/dir X (▷/inv X x) ≡ step X x
▷/beta = refl


postulate
  ► : (X : tp pos) → tp pos
  ►/decode : ∀ {X} → val (► X) ≡ sub (cmp (F X)) (image _ _ λ x → step (F X) (ret x))
  {-# REWRITE ►/decode #-}


postulate
  bool : tp pos
  tt ff : val bool

boolc : tp pos
boolc = ► bool


-- This version of the dependent product costs a step to apply.
Πc : (A : tp pos) (X : val A → tp neg) → tp neg
Πc A X = Π A λ x → ▷ (X x)
