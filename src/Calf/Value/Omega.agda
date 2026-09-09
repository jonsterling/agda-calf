module Calf.Value.Omega where

open import Cubical.Data.Nat
  using (ℕ; zero; suc; HasFromNat) renaming (_+_ to _+ℕ_)
open import Data.Unit using (⊤)

open import Calf.Value

data ω₀ : 𝒱 where
  zero : ω₀
  suc : (n : ω₀) → ω₀
  rel : (𝕚 : 𝟚) (n : ω₀) → ω₀
  rel-0𝟚 : ∀ n → rel 0𝟚 n ≡ n
  rel-1𝟚 : ∀ n → rel 1𝟚 n ≡ suc n

ω₀-elimProp : (P : ω₀ → 𝒱) → (∀ n → isProp (P n))
  → P zero → (∀ n → P n → P (suc n)) → (∀ 𝕚 n → P n → P (rel 𝕚 n)) → ∀ n → P n
ω₀-elimProp P isPropP z s r = go
  where
    go : ∀ n → P n
    go zero = z
    go (suc n) = s n (go n)
    go (rel 𝕚 n) = r 𝕚 n (go n)
    go (rel-0𝟚 n i) = isProp→PathP (λ i → isPropP (rel-0𝟚 n i)) (r 0𝟚 n (go n)) (go n) i
    go (rel-1𝟚 n i) = isProp→PathP (λ i → isPropP (rel-1𝟚 n i)) (r 1𝟚 n (go n)) (s n (go n)) i

infixl 6 _+₀_

_+₀_ : ω₀ → ω₀ → ω₀
zero +₀ n = n
suc m +₀ n = suc (m +₀ n)
rel 𝕚 m +₀ n = rel 𝕚 (m +₀ n)
rel-0𝟚 m i +₀ n = rel-0𝟚 (m +₀ n) i
rel-1𝟚 m i +₀ n = rel-1𝟚 (m +₀ n) i

+₀-identityʳ : ∀ n → n +₀ zero ≡ n
+₀-identityʳ zero = refl
+₀-identityʳ (suc n) = cong suc (+₀-identityʳ n)
+₀-identityʳ (rel 𝕚 n) = cong (rel 𝕚) (+₀-identityʳ n)
+₀-identityʳ (rel-0𝟚 n i) = cong (λ x → rel-0𝟚 x i) (+₀-identityʳ n)
+₀-identityʳ (rel-1𝟚 n i) = cong (λ x → rel-1𝟚 x i) (+₀-identityʳ n)

+₀-assoc : ∀ m n o → (m +₀ n) +₀ o ≡ m +₀ (n +₀ o)
+₀-assoc zero         _ _ = refl
+₀-assoc (suc m)      n o = cong suc (+₀-assoc m n o)
+₀-assoc (rel 𝕚 m)    n o = cong (rel 𝕚) (+₀-assoc m n o)
+₀-assoc (rel-0𝟚 m i) n o = cong (λ x → rel-0𝟚 x i) (+₀-assoc m n o)
+₀-assoc (rel-1𝟚 m i) n o = cong (λ x → rel-1𝟚 x i) (+₀-assoc m n o)

ℕ→ω₀ : ℕ → ω₀
ℕ→ω₀ zero = zero
ℕ→ω₀ (suc n) = suc (ℕ→ω₀ n)

ω : 𝒱
ω = ∥ ω₀ ∥ᴾ

isPreorderω : isPreorder ω
isPreorderω = isPreorderᴾ

ℕ→ω : ℕ → ω
ℕ→ω = ηᴾ ∘ ℕ→ω₀

instance
  fromNatω : HasFromNat ω
  fromNatω = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ℕ→ω n }

infixl 6 _+_

0ω 1ω : ω
0ω = ℕ→ω 0
1ω = ℕ→ω 1

_+_ : ω → ω → ω
_+_ = map2ᴾ _+₀_

open import Algebra.Definitions {A = ω} _≡_

+-identityˡ : LeftIdentity 0ω _+_
+-identityˡ = rec-unique isPreorderᴾ (0ω +_) (λ n → n) λ _ → refl

+-identityʳ : RightIdentity 0ω _+_
+-identityʳ = rec-unique isPreorderᴾ (_+ 0ω) (λ n → n) λ n → cong ηᴾ (+₀-identityʳ n)

+-assoc : Associative _+_
+-assoc m n o =
  funExt⁻
    (rec-unique2 (isLocalΠ λ _ → isPreorderᴾ)
      (λ m n o → (m + n) + o)
      (λ m n o → m + (n + o))
      (λ x y → funExt (rec-unique isPreorderᴾ _ _ λ z → cong ηᴾ (+₀-assoc x y z)))
      m n)
    o

⊑-suc : ∀ c → c ⊑ 1ω + c
⊑-suc c =
    (λ 𝕚 → mapᴾ (rel 𝕚) c)
  , rec-unique isPreorderᴾ (mapᴾ (rel 0𝟚)) (λ c → c) (λ n → cong ηᴾ (rel-0𝟚 n)) c
  , rec-unique isPreorderᴾ (mapᴾ (rel 1𝟚)) (1ω +_) (λ n → cong ηᴾ (rel-1𝟚 n)) c

private
  isSetω : isSet ω
  isSetω = isPreorder→isSet isPreorderω

  isThinω : isThin ω
  isThinω = isPreorder→isThin isPreorderω

  sucω : ω → ω
  sucω = mapᴾ suc

  relω : 𝟚 → ω → ω
  relω 𝕚 = mapᴾ (rel 𝕚)

  rel-suc : ∀ 𝕚 n → ηᴾ (rel 𝕚 (suc n)) ≡ ηᴾ (suc (rel 𝕚 n))
  rel-suc 𝕚 n =
    funExt⁻
      (isThin→𝟚-injective isThinω
        (cong ηᴾ (rel-0𝟚 (suc n)) ∙ sym (cong (sucω ∘ ηᴾ) (rel-0𝟚 n)))
        (cong ηᴾ (rel-1𝟚 (suc n)) ∙ sym (cong (sucω ∘ ηᴾ) (rel-1𝟚 n))))
      𝕚

  rel-rel : ∀ 𝕚 𝕛 n → ηᴾ (rel 𝕚 (rel 𝕛 n)) ≡ ηᴾ (rel 𝕛 (rel 𝕚 n))
  rel-rel 𝕚 𝕛 n =
    funExt⁻
      (isThin→𝟚-injective isThinω
        (cong ηᴾ (rel-0𝟚 (rel 𝕛 n)) ∙ sym (cong (relω 𝕛 ∘ ηᴾ) (rel-0𝟚 n)))
        (cong ηᴾ (rel-1𝟚 (rel 𝕛 n)) ∙ sym (rel-suc 𝕛 n) ∙ sym (cong (relω 𝕛 ∘ ηᴾ) (rel-1𝟚 n))))
      𝕚

  +-suc : ∀ m n → ηᴾ (m +₀ suc n) ≡ ηᴾ (suc (m +₀ n))
  +-suc m n =
    ω₀-elimProp (λ m → ηᴾ (m +₀ suc n) ≡ ηᴾ (suc (m +₀ n))) (λ _ → isSetω _ _)
      refl
      (λ m ih → cong sucω ih)
      (λ 𝕚 m ih → cong (relω 𝕚) ih ∙ rel-suc 𝕚 (m +₀ n))
      m

  +-rel : ∀ m 𝕚 n → ηᴾ (m +₀ rel 𝕚 n) ≡ ηᴾ (rel 𝕚 (m +₀ n))
  +-rel m 𝕚 n =
    ω₀-elimProp (λ m → ηᴾ (m +₀ rel 𝕚 n) ≡ ηᴾ (rel 𝕚 (m +₀ n))) (λ _ → isSetω _ _)
      refl
      (λ m ih → cong sucω ih ∙ sym (rel-suc 𝕚 (m +₀ n)))
      (λ 𝕛 m ih → cong (relω 𝕛) ih ∙ rel-rel 𝕛 𝕚 (m +₀ n))
      m

  +₀-comm : ∀ m n → ηᴾ (m +₀ n) ≡ ηᴾ (n +₀ m)
  +₀-comm m n =
    ω₀-elimProp (λ n → ηᴾ (m +₀ n) ≡ ηᴾ (n +₀ m)) (λ _ → isSetω _ _)
      (cong ηᴾ (+₀-identityʳ m))
      (λ n ih → +-suc m n ∙ cong sucω ih)
      (λ 𝕚 n ih → +-rel m 𝕚 n ∙ cong (relω 𝕚) ih)
      n

+-comm : Commutative _+_
+-comm = rec-unique2 isPreorderᴾ _+_ (λ m n → n + m) +₀-comm

isAlgorithmicω : isAlgorithmic ω
isAlgorithmicω beh =
  isContrᴾ zero
    (ω₀-elimProp (λ n → 0ω ≡ ηᴾ n) (λ _ → isSetω _ _)
      refl
      (λ n ih → ih ∙ ⊑-BEH beh (⊑-suc (ηᴾ n)))
      (λ 𝕚 n ih → ih ∙ cong ηᴾ (sym (rel-0𝟚 n) ∙ cong (λ 𝕛 → rel 𝕛 n) (isContr→isProp (isAlgorithmic𝟚 beh) 0𝟚 𝕚))))
