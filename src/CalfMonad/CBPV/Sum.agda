{-# OPTIONS --erased-cubical --rewriting #-}

open import CalfMonad.Monad

module CalfMonad.CBPV.Sum {ℓ M} (monad : Monad {ℓ} {ℓ} M) where

open Monad monad

open Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path renaming (_≡_ to Path)
open import Agda.Builtin.Equality.Rewrite

open import CalfMonad.Prelude
open import CalfMonad.CBPV monad renaming (map to F-map)
open import CalfMonad.Monad.Solver
open MonadSolver monad

open import Data.Sum renaming (map to ⊎-map)
open import Data.Product renaming (swap to ×-swap)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Function
open import Relation.Binary.PropositionalEquality.Core
open ≡-Reasoning

record Coeq {X Y} (f g : X →⁻ Y) : Set (lsuc ℓ) where
  field
    Q       : tp-
    q       : Y →⁻ Q
    q∘f=q∘g : ∀ x → q $⁻ (f $⁻ x) ≡ q $⁻ (g $⁻ x)
    u       : ∀ {Z} (h : Y →⁻ Z) (h∘f=h∘g : ∀ x → h $⁻ (f $⁻ x) ≡ h $⁻ (g $⁻ x)) → Q →⁻ Z
    u∘q=h   : ∀ {Z} (h : Y →⁻ Z) (h∘f=h∘g : ∀ x → h $⁻ (f $⁻ x) ≡ h $⁻ (g $⁻ x)) y → u h h∘f=h∘g $⁻ (q $⁻ y) ≡ h $⁻ y
    u=u′    : ∀ {Z} (h : Y →⁻ Z) (h∘f=h∘g : ∀ x → h $⁻ (f $⁻ x) ≡ h $⁻ (g $⁻ x)) (u′ : Q →⁻ Z) (u′∘q=h : ∀ y → u′ $⁻ (q $⁻ y) ≡ h $⁻ y) y → u h h∘f=h∘g $⁻ y ≡ u′ $⁻ y

module _ (A : tp+) (X : A → tp-) where
  private
    f : F (Σ A λ a → M (U (X a))) →⁻ F (Σ A λ a → U (X a))
    f = F-map λ (a , e) → a , bind (X a) e id

    g : F (Σ A λ a → M (U (X a))) →⁻ F (Σ A λ a → U (X a))
    g $⁻ e = e >>= λ (a , e) → e >>= pure ∘ (a ,_)
    g .$⁻-bind e f = >>=->>= e f _

    postulate
      coeq : Coeq f g

  open Coeq coeq
  open Coeq coeq public using () renaming (Q to Σ-)

  inj : ∀ a → X a →⁻ Σ-
  inj a $⁻ x = q $⁻ pure (a , x)
  inj a .$⁻-bind e f =
    q $⁻ pure (a , bind (X a) e f)                                              ≡˘⟨ cong (q $⁻_ ∘ pure ∘ (a ,_) ∘ bind (X a) e) (funext λ _ → pure-bind (X a) _ id) ⟩
    q $⁻ pure (a , bind (X a) e (λ b → bind (X a) (pure (f b)) id))             ≡˘⟨ cong (q $⁻_ ∘ pure ∘ (a ,_)) (>>=-bind (X a) e _ id) ⟩
    q $⁻ pure (a , bind (X a) (e >>= pure ∘ f) id)                              ≡⟨ cong (q $⁻_) solve ⟩
    q $⁻ (pure (a , e >>= pure ∘ f) >>= λ (a , e) → pure (a , bind (X a) e id)) ≡⟨ q∘f=q∘g _ ⟩
    q $⁻ (pure (a , e >>= pure ∘ f) >>= λ (a , e) → e >>= λ x → pure (a , x))   ≡⟨ cong (q $⁻_) solve ⟩
    q $⁻ (id (e >>= pure ∘ f) >>= λ x → pure (a , x))                           ≡⟨⟩
    q $⁻ ((e >>= pure ∘ f) >>= λ x → pure (a , x))                              ≡⟨ cong (q $⁻_) solve ⟩
    q $⁻ (e >>= λ b → pure (a , f b))                                           ≡⟨ q .$⁻-bind e _ ⟩
    bind Q e (λ b → q $⁻ pure (a , f b))                                        ∎

  [_] : ∀ {Y} → (∀ a → X a →⁻ Y) → Σ- →⁻ Y
  [_] {Y} inj′ = u inj″ λ e →
    bind Y (e >>= λ (a , e) → pure (a , bind (X a) e id)) (λ (a , x) → inj′ a $⁻ x)     ≡⟨ >>=-bind Y e _ _ ⟩
    bind Y e (λ (a , e) → bind Y (pure (a , bind (X a) e id)) λ (a , x) → inj′ a $⁻ x)  ≡⟨ cong (bind Y e) (funext λ _ → pure-bind Y _ _) ⟩
    bind Y e (λ (a , e) → inj′ a $⁻ bind (X a) e id)                                    ≡⟨ cong (bind Y e) (funext λ _ → inj′ _ .$⁻-bind _ id) ⟩
    bind Y e (λ (a , e) → bind Y e λ x → inj′ a $⁻ x)                                   ≡˘⟨ cong (bind Y e) (funext λ _ → cong (bind Y _) (funext λ _ → pure-bind Y _ _)) ⟩
    bind Y e (λ (a , e) → bind Y e λ x → bind Y (pure (a , x)) λ (a , x) → inj′ a $⁻ x) ≡˘⟨ cong (bind Y e) (funext λ _ → >>=-bind Y _ _ _) ⟩
    bind Y e (λ (a , e) → bind Y (e >>= pure ∘ (a ,_)) λ (a , x) → inj′ a $⁻ x)         ≡˘⟨ >>=-bind Y e _ _ ⟩
    bind Y (e >>= λ (a , e) → e >>= pure ∘ (a ,_)) (λ (a , x) → inj′ a $⁻ x)            ∎
    where
      inj″ : F (Σ A λ a → U (X a)) →⁻ Y
      inj″ $⁻ e = bind Y e λ (a , x) → inj′ a $⁻ x
      inj″ .$⁻-bind e f = >>=-bind Y e f _

  [-]-inj : ∀ {Y} (inj′ : ∀ a → X a →⁻ Y) a x → [ inj′ ] $⁻ (inj a $⁻ x) ≡ inj′ a $⁻ x
  [-]-inj {Y} inj′ a x =
    u _ _ $⁻ (q $⁻ pure (a , x))                    ≡⟨ u∘q=h _ _ _ ⟩
    bind Y (pure (a , x)) (λ (a , x) → inj′ a $⁻ x) ≡⟨ pure-bind Y _ _ ⟩
    inj′ a $⁻ x                                     ∎

module Test-1 (X : tp-) where
  f : F (M (U X)) →⁻ F (U X)
  f = F-map λ e → bind X e id

  g : F (M (U X)) →⁻ F (U X)
  g $⁻ e = e >>= id
  g .$⁻-bind e f = >>=->>= e f _

  open Coeq

  coeq : Coeq f g
  coeq .Q = X
  coeq .q $⁻ e = bind X e id
  coeq .q .$⁻-bind e f = >>=-bind X e f id
  coeq .q∘f=q∘g e =
    bind X (e >>= λ e → pure (bind X e id)) id      ≡⟨ >>=-bind X e _ id ⟩
    bind X e (λ e → bind X (pure (bind X e id)) id) ≡⟨ cong (bind X e) (funext λ _ → pure-bind X _ id) ⟩
    bind X e (λ e → bind X e id)                    ≡˘⟨ >>=-bind X e id id ⟩
    bind X (e >>= id) id                            ∎
  coeq .u h h∘f=h∘g $⁻ x = h $⁻ pure x
  coeq .u {Z} h h∘f=h∘g .$⁻-bind e f =
    h $⁻ pure (bind X e f)                                    ≡˘⟨ cong (h $⁻_ ∘ pure ∘ bind X e) (funext λ _ → pure-bind X _ id) ⟩
    h $⁻ pure (bind X e (λ a → bind X (pure (f a)) id))       ≡˘⟨ cong (h $⁻_ ∘ pure) (>>=-bind X e _ id) ⟩
    h $⁻ pure (bind X (e >>= pure ∘ f) id)                    ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ (pure (e >>= pure ∘ f) >>= λ e → pure (bind X e id)) ≡⟨ h∘f=h∘g _ ⟩
    h $⁻ (pure (e >>= pure ∘ f) >>= id)                       ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ (id (e >>= pure ∘ f))                                ≡⟨⟩
    h $⁻ (e >>= pure ∘ f)                                     ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ (e >>= pure ∘ f)                                     ≡⟨ h .$⁻-bind e (pure ∘ f) ⟩
    bind Z e (λ a → h $⁻ pure (f a))                          ∎
  coeq .u∘q=h h h∘f=h∘g e =
    h $⁻ (pure (bind X e id))                  ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ (pure e >>= λ e → pure (bind X e id)) ≡⟨ h∘f=h∘g _ ⟩
    h $⁻ (pure e >>= id)                       ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ e                                     ∎
  coeq .u=u′ h h∘f=h∘g u′ u′∘q=h x =
    h $⁻ pure x              ≡˘⟨ u′∘q=h _ ⟩
    u′ $⁻ bind X (pure x) id ≡⟨ cong (u′ $⁻_) (pure-bind X x id) ⟩
    u′ $⁻ x                  ∎

module Test-F (A : tp+) (B : A → tp+) where
  f : F (Σ A λ a → M (M (B a))) →⁻ F (Σ A λ a → M (B a))
  f = F-map λ (a , e) → a , e >>= id

  g : F (Σ A λ a → M (M (B a))) →⁻ F (Σ A λ a → M (B a))
  g $⁻ e = e >>= λ (a , e) → e >>= pure ∘ (a ,_)
  g .$⁻-bind e f = >>=->>= e f _

  open Coeq

  coeq : Coeq f g
  coeq .Q = F (Σ A B)
  coeq .q $⁻ e = e >>= λ (a , e) → e >>= pure ∘ (a ,_)
  coeq .q .$⁻-bind e f = >>=->>= e f _
  coeq .q∘f=q∘g e =
    (e >>= λ (a , e) → pure (a , e >>= id)) >>= (λ (a , e) → e >>= pure ∘ (a ,_)) ≡⟨ solve ⟩
    e >>= (λ (a , e) → id (e >>= id) >>= pure ∘ (a ,_))                           ≡⟨⟩
    e >>= (λ (a , e) → (e >>= id) >>= pure ∘ (a ,_))                              ≡⟨ solve ⟩
    (e >>= λ (a , e) → e >>= pure ∘ (a ,_)) >>= (λ (a , e) → e >>= pure ∘ (a ,_)) ∎
  coeq .u h h∘f=h∘g = h ∘⁻ F-map λ (a , b) → a , pure b
  coeq .u∘q=h h h∘f=h∘g e =
    h $⁻ ((e >>= λ (a , e) → e >>= pure ∘ (a ,_)) >>= λ (a , b) → pure (a , pure b))            ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ (e >>= λ (a , e) → (e >>= pure ∘ pure) >>= pure ∘ (a ,_))                              ≡⟨⟩
    h $⁻ (e >>= λ (a , e) → id (e >>= pure ∘ pure) >>= pure ∘ (a ,_))                           ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ ((e >>= λ (a , e) → pure (a , e >>= pure ∘ pure)) >>= λ (a , e) → e >>= pure ∘ (a ,_)) ≡˘⟨ h∘f=h∘g (e >>= λ (a , e) → pure (a , e >>= pure ∘ pure)) ⟩
    h $⁻ ((e >>= λ (a , e) → pure (a , e >>= pure ∘ pure)) >>= λ (a , e) → pure (a , e >>= id)) ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ (e >>= λ (a , e) → pure (a , (e >>= pure ∘ pure) >>= id))                              ≡⟨ cong (h $⁻_ ∘ (e >>=_)) (funext λ _ → cong (pure ∘ (_ ,_)) solve) ⟩
    h $⁻ (e >>= λ (a , e) → pure (a , e >>= λ b → id (pure b)))                                 ≡⟨⟩
    h $⁻ (e >>= λ (a , e) → pure (a , e >>= pure))                                              ≡⟨ cong (h $⁻_ ∘ (e >>=_)) (funext λ _ → cong (pure ∘ (_ ,_)) solve) ⟩
    h $⁻ (e >>= pure)                                                                           ≡⟨ cong (h $⁻_) solve ⟩
    h $⁻ e                                                                                      ∎
  coeq .u=u′ h h∘f=h∘g u′ u′∘q=h e =
    h $⁻ (e >>= λ (a , b) → pure (a , pure b))                                        ≡˘⟨ u′∘q=h _ ⟩
    u′ $⁻ ((e >>= λ (a , b) → pure (a , pure b)) >>= λ (a , e) → e >>= pure ∘ (a ,_)) ≡⟨ cong (u′ $⁻_) solve ⟩
    u′ $⁻ (e >>= λ (a , b) → id (pure b) >>= pure ∘ (a ,_))                           ≡⟨⟩
    u′ $⁻ (e >>= λ (a , b) → pure b >>= pure ∘ (a ,_))                                ≡⟨ cong (u′ $⁻_) solve ⟩
    u′ $⁻ e                                                                           ∎

module _ {a A x y} where
  ≡⇒Path : x ≡ y → Path {a} {A} x y
  ≡⇒Path refl _ = x

  Path⇒≡ : Path {a} {A} x y → x ≡ y
  Path⇒≡ p = primTransp (λ i → x ≡ p i) i0 refl

  ≡⇒Path⇒≡ : ∀ p → Path (Path⇒≡ (≡⇒Path p)) p
  ≡⇒Path⇒≡ refl = λ i → primTransp (λ _ → x ≡ x) i refl

module _ {a A x y} where
  Path⇒≡⇒Path : ∀ p → Path (≡⇒Path (Path⇒≡ {a} {A} {x} {y} p)) p
  Path⇒≡⇒Path p = primTransp (λ i → Path (≡⇒Path (Path⇒≡ (λ j → p (primIMin i j)))) λ j → p (primIMin i j)) i0 λ i → ≡⇒Path (≡⇒Path⇒≡ refl i)

module _ {a} {A : Set a} {r} where
  data Quot (R : A → A → Set r) : Set (a ⊔ r) where
    quot : A → Quot R
    rel′ : ∀ x₁ x₂ → R x₁ x₂ → Path (quot x₁) (quot x₂)
    squash′ : ∀ (x₁ x₂ : Quot R) (p q : Path x₁ x₂) → Path p q

  module _ {R : A → A → Set r} where
    rel : ∀ x₁ x₂ → R x₁ x₂ → quot x₁ ≡ quot x₂
    rel x₁ x₂ r = Path⇒≡ (rel′ {R} x₁ x₂ r)

    squash : (x₁ x₂ : Quot R) (p q : x₁ ≡ x₂) → p ≡ q
    squash x₁ x₂ p q = Path⇒≡ (primTransp (λ i → Path (≡⇒Path⇒≡ p i) (≡⇒Path⇒≡ q i)) i0 λ i → Path⇒≡ (squash′ x₁ x₂ (≡⇒Path p) (≡⇒Path q) i))

    module _ {b} {B : Set b} (Bquot : A → B) (Brel : ∀ x₁ x₂ → R x₁ x₂ → Path (Bquot x₁) (Bquot x₂)) (Bsquash : ∀ x₁ x₂ (p q : Path x₁ x₂) → Path p q) where
      Quot-rec′ : Quot R → B
      Quot-rec′ (quot x) = Bquot x
      Quot-rec′ (rel′ x₁ x₂ r i) = Brel x₁ x₂ r i
      Quot-rec′ (squash′ x₁ x₂ p q i j) = Bsquash (Quot-rec′ x₁) (Quot-rec′ x₂) (λ k → Quot-rec′ (p k)) (λ k → Quot-rec′ (q k)) i j

    module _ {b} {B : Set b} (Bquot : A → B) (Brel : ∀ x₁ x₂ → R x₁ x₂ → Bquot x₁ ≡ Bquot x₂) (Bsquash : (x₁ x₂ : B) (p q : x₁ ≡ x₂) → p ≡ q) where
      Quot-rec : Quot R → B
      Quot-rec = Quot-rec′ Bquot (λ x₁ x₂ r → ≡⇒Path (Brel x₁ x₂ r)) λ x₁ x₂ p q → primTransp (λ i → Path (Path⇒≡⇒Path p i) (Path⇒≡⇒Path q i)) i0 λ i → ≡⇒Path (≡⇒Path (Bsquash x₁ x₂ (Path⇒≡ p) (Path⇒≡ q)) i)

    postulate
      Quot-choice : (x : Quot R) → Σ A λ a → quot a ≡ x

cong₂′ : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c} (f : ∀ x → B x → C) {x y u v} x≡y → subst B x≡y u ≡ v → f x u ≡ f y v
cong₂′ f refl refl = refl

postulate
  Shift : ∀ {a} (A : Set a) b → Set b
  Shift/mk : ∀ {a} {A : Set a} b → A → Shift A b
  Shift/out : ∀ {a} {A : Set a} {b} → Shift A b → A
  Shift/beta : ∀ {a} {A : Set a} b (x : A) → Shift/out (Shift/mk b x) ≡ x
  {-# REWRITE Shift/beta #-}

{-
module _ {X Y} (f g : X →⁻ Y) where
  data R : U Y → U Y → tp+

  UE : tp+
  UE = Σ (U Y × U Y) λ (y₁ , y₂) → R y₁ y₂

  data R where
    R/trunc : ∀ {y₁ y₂} r₁ r₂ → PathP (λ _ → R y₁ y₂) r₁ r₂
    R/refl : ∀ y → R y y
    R/sym : ∀ {y₁ y₂} → R y₁ y₂ → R y₂ y₁
    R/trans : ∀ {y₁ y₂ y₃} → R y₁ y₂ → R y₂ y₃ → R y₁ y₃
    R/base : ∀ x → R (f $⁻ x) (g $⁻ x)
    R/closed : ∀ (A : Shift (Set ℓ) lzero) (e : M (Shift/out A)) (f : Shift/out A → UE) → R (bind Y e (proj₁ ∘ proj₁ ∘ f)) (bind Y e (proj₂ ∘ proj₁ ∘ f))

  R/trunc′ : ∀ {y₁ y₂} (r₁ r₂ : R y₁ y₂) → r₁ ≡ r₂
  R/trunc′ r₁ r₂ = Path⇒≡ (R/trunc r₁ r₂)

  E : tp-
  U E = UE
  bind E e f = bind (Y ×⁻ Y) e (proj₁ ∘ f) , R/closed (Shift/mk _ _) e f
  pure-bind E a f = cong₂′ _,_ (pure-bind (Y ×⁻ Y) a _) (R/trunc′ _ _)
  >>=-bind E e f g = cong₂′ _,_ (>>=-bind (Y ×⁻ Y) e f _) (R/trunc′ _ _)

  E↪Y×⁻Y : E →⁻ (Y ×⁻ Y)
  E↪Y×⁻Y ._$⁻_ = proj₁
  E↪Y×⁻Y .$⁻-bind e f = refl

  p₁ : E →⁻ Y
  p₁ = proj₁⁻ {Y} {Y} ∘⁻ E↪Y×⁻Y

  p₂ : E →⁻ Y
  p₂ = proj₂⁻ {Y} {Y} ∘⁻ E↪Y×⁻Y

  UY/UE : tp+
  UY/UE = Quot R

  p : U Y → UY/UE
  p = inj

  r : UY/UE → U Y
  r = Quot-choice

  rp-1 : U Y → UE
  rp-1 y .proj₁ = r (p y) , y
  rp-1 y .proj₂ = Quot-choice-rel-inj {R = R} y

  p∘r≡1 : ∀ x → p (r x) ≡ x
  p∘r≡1 = Quot-inj-choice

  M-U-p₁ : M UE → M (U Y)
  M-U-p₁ = _>>= pure ∘ (proj₁ ∘ proj₁)

  M-U-p₂ : M UE → M (U Y)
  M-U-p₂ = _>>= pure ∘ (proj₂ ∘ proj₁)

  M-p : M (U Y) → M UY/UE
  M-p = _>>= pure ∘ p

  M-UE-UE : M UE → UE
  M-UE-UE e = bind E e id

  M-UY-UY : M (U Y) → U Y
  M-UY-UY e = bind Y e id

  MUY/UE-M-UY : M UY/UE → M (U Y)
  MUY/UE-M-UY = _>>= pure ∘ r

  MUY/UE-UY/UE : M UY/UE → UY/UE
  MUY/UE-UY/UE = p ∘ M-UY-UY ∘ MUY/UE-M-UY

  Y/E : tp-
  U Y/E = UY/UE
  bind Y/E e f = p (bind Y e (r ∘ f))
  pure-bind Y/E a f rewrite pure-bind Y a (r ∘ f) = p∘r≡1 (f a)
  >>=-bind Y/E e f g rewrite >>=-bind Y e f (r ∘ g) = rel′ (R/closed (Shift/mk _ _) e λ a → (bind Y (f a) (r ∘ g) , r (p (bind Y (f a) (r ∘ g)))) , R/sym (Quot-choice-rel-inj {R = R} (bind Y (f a) (r ∘ g))))

  p′ : Y →⁻ Y/E
  p′ ._$⁻_ = p
  p′ .$⁻-bind e f = rel′ (R/closed (Shift/mk _ _) e λ x → (f x , r (p (f x))) , R/sym (Quot-choice-rel-inj {R = R} (f x)))

  is-fork : ∀ x → p′ $⁻ (p₁ $⁻ x) ≡ p′ $⁻ (p₂ $⁻ x)
  is-fork (_ , r) = rel′ r

  is-univ : ∀ {Z} (h : Y →⁻ Z) → (∀ x → h $⁻ (p₁ $⁻ x) ≡ h $⁻ (p₂ $⁻ x)) → Y/E →⁻ Z
  is-univ h eq $⁻ x = h $⁻ r x
  is-univ h eq .$⁻-bind e i rewrite sym (h .$⁻-bind e (r ∘ i)) = {!!}
    where
      foo : ∀ {y₁ y₂} → R y₁ y₂ → h $⁻ y₁ ≡ h $⁻ y₂
      foo (R/refl y) = refl
      foo (R/sym r) = sym (foo r)
      foo (R/trans r₁ r₂) = trans (foo r₁) (foo r₂)
      foo r@(R/base x) = eq ((f $⁻ x , g $⁻ x) , r)
      foo (R/closed A e f) = {!!}
      -- (h $⁻ bind Y e (λ x → proj₁ (proj₁ (f x)))) ≡ (h $⁻ bind Y e (λ x → proj₂ (proj₁ (f x))))
      foo (R/trunc r₁ r₂ i) = todo i
        where
          todo : PathP _ (foo r₁) (foo r₂)
          todo = {!!}
  -- f $⁻ r (p (bind Y e (r ∘ g))) ≡ f $⁻ bind Y e (r ∘ g)
  -}
