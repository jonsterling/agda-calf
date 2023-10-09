------------------------------------------------------------------------
-- The Calf library
--
-- Unit interval
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Interval.Base where

open import Algebra.Bundles.Raw
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.GCD
open import Data.Nat.Coprimality as C
  using (Coprime; coprime-/gcd; ¬0-coprimeTo-2+; coprime-+)
open import Data.Nat.DivMod using (/-monoˡ-≤)
open import Data.Nat.Divisibility using (_∣_; divides; ∣m+n∣m⇒∣n; ∣m∸n∣n⇒∣m)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc) hiding (module ℕ)
import Data.Nat.Properties as ℕ
open import Data.Product
open import Data.Sum.Base using (inj₂)
open import Function.Base using (id; _$_)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_; recompute)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_; _≢_; refl)
open import Data.Integer using (+_)
open import Data.Rational as ℚ using (ℚ)

------------------------------------------------------------------------
-- The unit interval in reduced form. Note that there is exactly one
-- way to represent every element of the unit interval.

record 𝕀 : Set where
  no-eta-equality; pattern

  constructor mk𝕀
  field
    numerator     : ℕ
    denominator-1 : ℕ
    .isCoprime    : Coprime numerator (suc denominator-1)
    .isContained  : numerator ℕ.≤ suc denominator-1

  denominator : ℕ
  denominator = suc denominator-1

open 𝕀 public using ()
  renaming
  ( numerator    to ↥_
  ; denominator  to ↧_
  )

mk𝕀+ : ∀ n d → .{{_ : ℕ.NonZero d}} → .(Coprime n d) → .(n ℕ.≤ d) → 𝕀
mk𝕀+ n (suc d) = mk𝕀 n d

------------------------------------------------------------------------
-- Equality of elements of the unit interval (coincides with _≡_)

infix 4 _≃_

_≃_ : Rel 𝕀 0ℓ
p ≃ q = (↥ p ℕ.* ↧ q) ≡ (↥ q ℕ.* ↧ p)

------------------------------------------------------------------------
-- Ordering of the unit interval

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≱_ _≮_ _≯_

data _≤_ : Rel 𝕀 0ℓ where
  *≤* : ∀ {p q} → (↥ p ℕ.* ↧ q) ℕ.≤ (↥ q ℕ.* ↧ p) → p ≤ q

data _<_ : Rel 𝕀 0ℓ where
  *<* : ∀ {p q} → (↥ p ℕ.* ↧ q) ℕ.< (↥ q ℕ.* ↧ p) → p < q

_≥_ : Rel 𝕀 0ℓ
x ≥ y = y ≤ x

_>_ : Rel 𝕀 0ℓ
x > y = y < x

_≰_ : Rel 𝕀 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel 𝕀 0ℓ
x ≱ y = ¬ (x ≥ y)

_≮_ : Rel 𝕀 0ℓ
x ≮ y = ¬ (x < y)

_≯_ : Rel 𝕀 0ℓ
x ≯ y = ¬ (x > y)

------------------------------------------------------------------------
-- Boolean ordering

infix 4 _≤ᵇ_

_≤ᵇ_ : 𝕀 → 𝕀 → Bool
p ≤ᵇ q = (↥ p ℕ.* ↧ q) ℕ.≤ᵇ (↥ q ℕ.* ↧ p)

------------------------------------------------------------------------
-- Constructing elements of the unit interval

-- A constructor for 𝕀 that takes two natural numbers, say 6 and 21,
-- and returns them in a normalized form, e.g. say 2 and 7

normalize : ∀ (m n : ℕ) .{{_ : ℕ.NonZero n}} .{{_ : m ℕ.≤ n}} → 𝕀
normalize m n {{_}} {{m≤n}} =
  mk𝕀+ (m ℕ./ gcd m n) (n ℕ./ gcd m n) (coprime-/gcd m n) (/-monoˡ-≤ (gcd m n) m≤n)
    where
      instance
        g≢0   = ℕ.≢-nonZero (gcd[m,n]≢0 m n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
        n/g≢0 = ℕ.≢-nonZero (n/gcd[m,n]≢0 m n {{gcd≢0 = g≢0}})

-- A constructor for 𝕀 that (unlike mk𝕀) automatically normalises its
-- arguments. See the constants section below for how to use this operator.

infixl 7 _/_

_/_ : (n : ℕ) (d : ℕ) .{{_ : ℕ.NonZero d}} .{{_ : n ℕ.≤ d}} → 𝕀
_/_ = normalize

------------------------------------------------------------------------
-- Conversion to rationals

toℚ : 𝕀 → ℚ
toℚ (mk𝕀 numerator denominator-1 isCoprime isContained) =
  ℚ.mkℚ (+ numerator) denominator-1 isCoprime

------------------------------------------------------------------------------
-- Some constants

instance
  instance-z≤n : ∀ {n} → zero ℕ.≤ n
  instance-z≤n = ℕ.z≤n

  instance-s≤s : ∀ {m n} → {{m ℕ.≤ n}} → suc m ℕ.≤ suc n
  instance-s≤s {{h}} = ℕ.s≤s h

0𝕀 : 𝕀
0𝕀 = 0 / 1

1𝕀 : 𝕀
1𝕀 = 1 / 1

½ : 𝕀
½ = 1 / 2

¼ : 𝕀
¼ = 1 / 4

⅓ : 𝕀
⅓ = 1 / 3

⅔ : 𝕀
⅔ = 2 / 3

------------------------------------------------------------------------
-- Simple predicates

NonZero : Pred 𝕀 0ℓ
NonZero p = ℕ.NonZero (↥ p)

NonOne : Pred 𝕀 0ℓ
NonOne p = ℕ.NonZero (𝕀.denominator-1 p)

-- Constructors

≢-nonZero : ∀ {p} → p ≢ 0𝕀 → NonZero p
≢-nonZero {mk𝕀 (suc _) _       _ _} _   = _
≢-nonZero {mk𝕀 zero    zero    _ _} p≢0 = contradiction refl p≢0
≢-nonZero {mk𝕀 zero    (suc _) c _} p≢0 = contradiction (λ {i} → C.recompute c {i}) ¬0-coprimeTo-2+

>-nonZero : ∀ {p} → p > 0𝕀 → NonZero p
>-nonZero {mk𝕀 (suc _) _ _ _} (*<* x) = _

------------------------------------------------------------------------------
-- Operations on elements of the unit interval

-- For explanation of the `@record{}` annotations see notes in the equivalent
-- place in `Data.Rational.Unnormalised.Base`.

infix  8 1-_
infixl 7 _∧_ _⊓_ _*_ _÷_
infixl 6 _∨_ _⊔_

1-_ : 𝕀 → 𝕀
1- p@record{isCoprime = isCoprime; isContained = isContained} =
  mk𝕀+ (↧ p ℕ.∸ ↥ p) (↧ p) (coprime-∸ isContained isCoprime) (ℕ.m∸n≤m (↧ p) (↥ p))
  where
    ∣m∸n∣m⇒∣n : ∀ i {m n} → n ℕ.≤ m → i ∣ m ℕ.∸ n → i ∣ m → i ∣ n
    ∣m∸n∣m⇒∣n i {m} {n} n≤m (divides p m∸n≡p*i) (divides q m≡q*i) =
      divides (q ℕ.∸ p) $ begin-equality
        n                   ≡˘⟨ ℕ.m∸[m∸n]≡n n≤m ⟩
        m ℕ.∸ (m ℕ.∸ n)     ≡⟨ P.cong₂ ℕ._∸_ m≡q*i m∸n≡p*i ⟩
        q ℕ.* i ℕ.∸ p ℕ.* i ≡˘⟨ ℕ.*-distribʳ-∸ i q p ⟩
        (q ℕ.∸ p) ℕ.* i     ∎
        where open ℕ.≤-Reasoning

    coprime-∸ : ∀ {m n} → m ℕ.≤ n → Coprime m n → Coprime (n ℕ.∸ m) n
    coprime-∸ m≤n c (d₁ , d₂) = c (∣m∸n∣m⇒∣n _ m≤n d₁ d₂ , d₂)


-- conjunction
_∧_ : 𝕀 → 𝕀 → 𝕀
p@record{isContained = isContained₁} ∧ q@record{isContained = isContained₂} =
  _/_
    (↥ p ℕ.* ↥ q)
    (↧ p ℕ.* ↧ q)
    {{_}}
    {{ℕ.*-mono-≤ {x = ↥ p} {y = ↧ p} {u = ↥ q} {v = ↧ q} isContained₁ isContained₂}}

-- disjunction
_∨_ : 𝕀 → 𝕀 → 𝕀
p@record{} ∨ q@record{} = 1- ((1- p) ∧ (1- q))

-- multiplication
_*_ = _∧_

-- division
_÷_ : (p q : 𝕀) .{{_ : NonZero q}} {_ : p ≤ q} → 𝕀
(p ÷ q) {*≤* h} =
  _/_
    (↥ p ℕ.* ↧ q)
    (↥ q ℕ.* ↧ p)
    {{ℕ.m*n≢0 (↥ q) (↧ p)}}
    {{h}}

-- max
_⊔_ : 𝕀 → 𝕀 → 𝕀
p@record{} ⊔ q@record{} = if p ≤ᵇ q then q else p

-- min
_⊓_ : 𝕀 → 𝕀 → 𝕀
p@record{} ⊓ q@record{} = if p ≤ᵇ q then p else q

------------------------------------------------------------------------
-- Raw bundles

∧-rawMagma : RawMagma 0ℓ 0ℓ
∧-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _∧_
  }

∧-1-rawMonoid : RawMonoid 0ℓ 0ℓ
∧-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _∧_
  ; ε   = 1𝕀
  }

∨-rawMagma : RawMagma 0ℓ 0ℓ
∨-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _∨_
  }

∨-0-rawMonoid : RawMonoid 0ℓ 0ℓ
∨-0-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _∨_
  ; ε   = 0𝕀
  }
