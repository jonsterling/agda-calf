module Calf.Core.Cost where

open import Cubical.Data.Nat
  using (ℕ; zero; suc; iter) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
import Cubical.Data.Nat.Properties as Nat

open import Calf.Value
open import Calf.Value.Omega
open import Calf.Value.Unit

open import Cubical.Data.Nat.Literals public

module _ {A : 𝒱} where
  open import Algebra.Definitions {A = A} _≡_ public

#_ = fromNat

opaque
  ℂ : 𝒱
  ℂ = ω

  isPreorderℂ : isPreorder ℂ
  isPreorderℂ = isPreorderω

  0ℂ : ℂ
  0ℂ = 0

  infixl 6 _+ℂ_
  _+ℂ_ : ℂ → ℂ → ℂ
  _+ℂ_ = _+_

  +ℂ-identityˡ : LeftIdentity 0ℂ _+ℂ_
  +ℂ-identityˡ = +-identityˡ

  +ℂ-identityʳ : RightIdentity 0ℂ _+ℂ_
  +ℂ-identityʳ = +-identityʳ

  +ℂ-assoc : Associative _+ℂ_
  +ℂ-assoc = +-assoc

  +ℂ-comm : Commutative _+ℂ_
  +ℂ-comm = +-comm

  isAlgorithmicℂ : isAlgorithmic ℂ
  isAlgorithmicℂ = isAlgorithmicω

  1ℂ : ℂ
  1ℂ = 1

  ⊑-sucℂ : ∀ c → c ⊑ 1ℂ +ℂ c
  ⊑-sucℂ = ⊑-suc

instance
  fromNatℂ : HasFromNat ℂ
  fromNatℂ = record { Constraint = λ _ → ⊤ ; fromNat = λ n → iter n (1ℂ +ℂ_) 0ℂ }

ℕ→ℂ : ℕ → ℂ
ℕ→ℂ n = # n

ℕ→ℂ-0 : ℕ→ℂ 0 ≡ 0ℂ
ℕ→ℂ-0 = refl

ℕ→ℂ-+ : ∀ m n → ℕ→ℂ (m +ℕ n) ≡ ℕ→ℂ m +ℂ ℕ→ℂ n
ℕ→ℂ-+ zero n = sym (+ℂ-identityˡ (ℕ→ℂ n))
ℕ→ℂ-+ (suc m) n = cong (1ℂ +ℂ_) (ℕ→ℂ-+ m n) ∙ sym (+ℂ-assoc _ _ _)

≤⇒⊑ℂ : ∀ {m n} → m ≤ n → ℕ→ℂ m ⊑ ℕ→ℂ n
≤⇒⊑ℂ (p , p+m≡n) = ⊑∙≡ (⊑-+ℂ p _) (cong ℕ→ℂ p+m≡n)
  where
    ⊑-+ℂ : ∀ p m → ℕ→ℂ m ⊑ ℕ→ℂ (p +ℕ m)
    ⊑-+ℂ zero m = ⊑-refl
    ⊑-+ℂ (suc p) m = ⊑-trans isPreorderℂ (⊑-+ℂ p m) (⊑-sucℂ (ℕ→ℂ (p +ℕ m)))

variable
  c c' c₁ c₂ : ℂ

_⊙_ : ℕ → ℂ → ℂ
zero ⊙ c = 0ℂ
suc n ⊙ c = c +ℂ (n ⊙ c)

⊙-distribˡ : ∀ n c₁ c₂ → n ⊙ (c₁ +ℂ c₂) ≡ (n ⊙ c₁) +ℂ (n ⊙ c₂)
⊙-distribˡ zero c₁ c₂ = sym (+ℂ-identityˡ 0ℂ)
⊙-distribˡ (suc n) c₁ c₂ =
    suc n ⊙ (c₁ +ℂ c₂)
  ≡⟨ cong ((c₁ +ℂ c₂) +ℂ_) (⊙-distribˡ n c₁ c₂) ⟩
    (c₁ +ℂ c₂) +ℂ ((n ⊙ c₁) +ℂ (n ⊙ c₂))
  ≡⟨ +ℂ-assoc c₁ c₂ ((n ⊙ c₁) +ℂ (n ⊙ c₂)) ⟩
    c₁ +ℂ (c₂ +ℂ ((n ⊙ c₁) +ℂ (n ⊙ c₂)))
  ≡⟨ cong (c₁ +ℂ_) (sym (+ℂ-assoc c₂ (n ⊙ c₁) (n ⊙ c₂))) ⟩
    c₁ +ℂ ((c₂ +ℂ (n ⊙ c₁)) +ℂ (n ⊙ c₂))
  ≡⟨ cong (λ c → c₁ +ℂ (c +ℂ (n ⊙ c₂))) (+ℂ-comm c₂ (n ⊙ c₁)) ⟩
    c₁ +ℂ (((n ⊙ c₁) +ℂ c₂) +ℂ (n ⊙ c₂))
  ≡⟨ cong (c₁ +ℂ_) (+ℂ-assoc (n ⊙ c₁) c₂ (n ⊙ c₂)) ⟩
    c₁ +ℂ ((n ⊙ c₁) +ℂ (c₂ +ℂ (n ⊙ c₂)))
  ≡⟨ sym (+ℂ-assoc c₁ (n ⊙ c₁) (c₂ +ℂ (n ⊙ c₂))) ⟩
    (suc n ⊙ c₁) +ℂ (suc n ⊙ c₂)
  ∎

⊙-distribʳ : ∀ n m c → (n +ℕ m) ⊙ c ≡ (n ⊙ c) +ℂ (m ⊙ c)
⊙-distribʳ zero m c = sym (+ℂ-identityˡ (m ⊙ c))
⊙-distribʳ (suc n) m c =
    (suc n +ℕ m) ⊙ c
  ≡⟨ cong (c +ℂ_) (⊙-distribʳ n m c) ⟩
    c +ℂ ((n ⊙ c) +ℂ (m ⊙ c))
  ≡⟨ sym (+ℂ-assoc c (n ⊙ c) (m ⊙ c)) ⟩
    (suc n ⊙ c) +ℂ (m ⊙ c)
  ∎
