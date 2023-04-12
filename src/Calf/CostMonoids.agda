{-# OPTIONS --prop --without-K --rewriting #-}

-- Common cost monoids.

module Calf.CostMonoids where

open import Calf.CostMonoid
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

ℕ-CostMonoid : CostMonoid
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℤ-CostMonoid : CostMonoid
ℤ-CostMonoid = record
  { ℂ = ℤ
  ; _+_ = _+_
  ; zero = 0ℤ
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Integer
    open import Data.Integer.Properties

ResourceMonoid : CostMonoid
ResourceMonoid = record
  { ℂ = ℕ × ℕ
  ; _+_ = _·_
  ; zero = 0 , 0
  ; _≤_ = _≤ᵣ_
  ; isCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = λ { refl refl → refl }
          }
        ; assoc = assoc
        }
      ; identity = identityˡ , identityʳ
      }
    ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ { refl → (≤-refl , ≤-refl) }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans h₁ h₁' , ≤-trans h₂' h₂
      }
    ; isMonotone = record { ∙-mono-≤ = ∙-mono-≤ᵣ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

    open import Data.Bool using (false; true)

    open import Algebra.Definitions _≡_
    open import Relation.Nullary
    open import Relation.Binary

    _·_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
    (p , p') · (q , q') with p' ≤? q
    ... | no ¬h = p , q' + (p' ∸ q)
    ... | yes h = p + (q ∸ p') , q'

    _≤ᵣ_ : ℕ × ℕ → ℕ × ℕ → Set
    (p , p') ≤ᵣ (q , q') = (p ≤ q) × (q' ≤ p')

    m≤n⇒m≤n+o : ∀ {m n o} → m ≤ n → m ≤ n + o
    m≤n⇒m≤n+o {m} {n} {o} h =
      begin
        m
      ≡˘⟨ +-identityʳ m ⟩
        m + 0
      ≤⟨ +-mono-≤ h z≤n ⟩
        n + o
      ∎
        where open ≤-Reasoning

    assoc : Associative _·_
    assoc (p , p') (q , q') (r , r') with q' ≤? r
    assoc (p , p') (q , q') (r , r') | no ¬h₁ with p' ≤? q
    assoc (p , p') (q , q') (r , r') | no ¬h₁ | no ¬h₂ with q' + (p' ∸ q) ≤? r
    assoc (p , p') (q , q') (r , r') | no ¬h₁ | no ¬h₂ | no ¬h₃ =
      let h₁ = ≰⇒≥ ¬h₁ in
      cong (p ,_)
        (begin
          r' + (q' + (p' ∸ q) ∸ r)
        ≡⟨ cong (r' +_) (+-∸-comm (p' ∸ q) h₁) ⟩
          r' + ((q' ∸ r) + (p' ∸ q))
        ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
          r' + (q' ∸ r) + (p' ∸ q)
        ∎)
          where open ≡-Reasoning
    assoc (p , p') (q , q') (r , r') | no ¬h₁ | no ¬h₂ | yes h₃ =
      let h₁ = ≰⇒≥ ¬h₁ in
      cong₂ _,_
        (begin
          p + (r ∸ (q' + (p' ∸ q)))
        ≡⟨ cong (p +_) (subst (λ n → (r ∸ n) ≡ 0) (≤-antisym (m≤n⇒m≤n+o h₁) h₃) (n∸n≡0 r)) ⟩
          p + 0
        ≡⟨ +-identityʳ p ⟩
          p
        ∎)
        (begin
          r'
        ≡˘⟨ +-identityʳ r' ⟩
          r' + 0
        ≡˘⟨ cong (r' +_) (subst (λ n → (n ∸ r) ≡ 0) (≤-antisym (m≤n⇒m≤n+o h₁) h₃) (n∸n≡0 r)) ⟩
          r' + (q' + (p' ∸ q) ∸ r)
        ≡⟨ cong (r' +_) (+-∸-comm (p' ∸ q) h₁) ⟩
          r' + ((q' ∸ r) + (p' ∸ q))
        ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
          r' + (q' ∸ r) + (p' ∸ q)
        ∎)
          where open ≡-Reasoning
    assoc (p , p') (q , q') (r , r') | no ¬h₁ | yes h₂ = {!   !}
    assoc (p , p') (q , q') (r , r') | yes h₁ = {!   !}

    identityˡ : LeftIdentity (0 , 0) _·_
    identityˡ (q , q') = cong₂ _,_ (+-identityˡ q) (+-identityˡ q')

    identityʳ : RightIdentity (0 , 0) _·_
    identityʳ (q , q') with q' ≤? 0
    ... | no ¬h = refl
    ... | yes z≤n = cong₂ _,_ (+-identityʳ q) refl

    ∙-mono-≤ᵣ : _·_ Preserves₂ _≤ᵣ_ ⟶ _≤ᵣ_ ⟶ _≤ᵣ_
    ∙-mono-≤ᵣ {p , p'} {q , q'} {r , r'} {s , s'} (h₁ , h₂) (h₁' , h₂') with p' ≤? r | q' ≤? s
    ... | no ¬p₁ | no ¬p₂ = h₁ , +-mono-≤ h₂' (∸-mono h₂ h₁')
    ... | no ¬p₁ | yes p₂ =
      let p₁ = ≰⇒≥ ¬p₁ in
      (
        begin
          p
        ≤⟨ h₁ ⟩
          q
        ≡˘⟨ +-identityʳ q ⟩
          q + 0
        ≡˘⟨ cong (q +_) (m≤n⇒m∸n≡0 p₁) ⟩
          q + (r ∸ p')
        ≤⟨ +-monoʳ-≤ q (∸-mono h₁' h₂) ⟩
          q + (s ∸ q')
        ∎
      ) , (
        begin
          s'
        ≤⟨ h₂' ⟩
          r'
        ≡˘⟨ +-identityʳ r' ⟩
          r' + 0
        ≡˘⟨ cong (r' +_) (m≤n⇒m∸n≡0 p₂) ⟩
          r' + (q' ∸ s)
        ≤⟨ +-monoʳ-≤ r' (∸-mono h₂ h₁') ⟩
          r' + (p' ∸ r)
        ∎
      )
        where open ≤-Reasoning
    ... | yes p₁ | no ¬p₂ =
      let p₂ = ≰⇒≥ ¬p₂ in
      (
        begin
          p + (r ∸ p')
        ≤⟨ +-monoʳ-≤ p (∸-mono h₁' h₂) ⟩
          p + (s ∸ q')
        ≡⟨ cong (p +_) (m≤n⇒m∸n≡0 p₂) ⟩
          p + 0
        ≡⟨ +-identityʳ p ⟩
          p
        ≤⟨ h₁ ⟩
          q
        ∎
      ) , (
        begin
          s' + (q' ∸ s)
        ≤⟨ +-monoʳ-≤ s' (∸-mono h₂ h₁') ⟩
          s' + (p' ∸ r)
        ≡⟨ cong (s' +_) (m≤n⇒m∸n≡0 p₁) ⟩
          s' + 0
        ≡⟨ +-identityʳ s' ⟩
          s'
        ≤⟨ h₂' ⟩
          r'
        ∎
      )
        where open ≤-Reasoning
    ... | yes p₁ | yes p₂ = +-mono-≤ h₁ (∸-mono h₁' h₂) , h₂'

ℕ-Work-ParCostMonoid : ParCostMonoid
ℕ-Work-ParCostMonoid = record
  { ℂ = ℕ
  ; _⊕_ = _+_
  ; 𝟘 = 0
  ; _⊗_ = _+_
  ; 𝟙 = 0
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isCommutativeMonoid = +-0-isCommutativeMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone-⊕ = record { ∙-mono-≤ = +-mono-≤ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℕ-Span-ParCostMonoid : ParCostMonoid
ℕ-Span-ParCostMonoid = record
  { ℂ = ℕ
  ; _⊕_ = _+_
  ; 𝟘 = 0
  ; _⊗_ = _⊔_
  ; 𝟙 = 0
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isCommutativeMonoid = ⊔-0-isCommutativeMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone-⊕ = record { ∙-mono-≤ = +-mono-≤ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = ⊔-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

combineParCostMonoids : ParCostMonoid → ParCostMonoid → ParCostMonoid
combineParCostMonoids pcm₁ pcm₂ = record
  { ℂ = ℂ pcm₁ × ℂ pcm₂
  ; _⊕_ = λ (a₁ , a₂) (b₁ , b₂) → _⊕_ pcm₁ a₁ b₁ , _⊕_ pcm₂ a₂ b₂
  ; 𝟘 = 𝟘 pcm₁ , 𝟘 pcm₂
  ; _⊗_ = λ (a₁ , a₂) (b₁ , b₂) → _⊗_ pcm₁ a₁ b₁ , _⊗_ pcm₂ a₂ b₂
  ; 𝟙 = 𝟙 pcm₁ , 𝟙 pcm₂
  ; _≤_ = λ (a₁ , a₂) (b₁ , b₂) → _≤_ pcm₁ a₁ b₁ × _≤_ pcm₂ a₂ b₂
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = λ h₁ h₂ →
              cong₂ _,_
                (cong₂ (_⊕_ pcm₁) (cong proj₁ h₁) (cong proj₁ h₂))
                (cong₂ (_⊕_ pcm₂) (cong proj₂ h₁) (cong proj₂ h₂))
          }
        ; assoc = λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) → cong₂ _,_ (⊕-assoc pcm₁ a₁ b₁ c₁) (⊕-assoc pcm₂ a₂ b₂ c₂)
        }
      ; identity =
        (λ (a₁ , a₂) → cong₂ _,_ (⊕-identityˡ pcm₁ a₁) (⊕-identityˡ pcm₂ a₂)) ,
        (λ (a₁ , a₂) → cong₂ _,_ (⊕-identityʳ pcm₁ a₁) (⊕-identityʳ pcm₂ a₂))
      }
    ; isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong = λ h₁ h₂ →
                cong₂ _,_
                  (cong₂ (_⊗_ pcm₁) (cong proj₁ h₁) (cong proj₁ h₂))
                  (cong₂ (_⊗_ pcm₂) (cong proj₂ h₁) (cong proj₂ h₂))
            }
          ; assoc = λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) → cong₂ _,_ (⊗-assoc pcm₁ a₁ b₁ c₁) (⊗-assoc pcm₂ a₂ b₂ c₂)
          }
        ; identity =
          (λ (a₁ , a₂) → cong₂ _,_ (⊗-identityˡ pcm₁ a₁) (⊗-identityˡ pcm₂ a₂)) ,
          (λ (a₁ , a₂) → cong₂ _,_ (⊗-identityʳ pcm₁ a₁) (⊗-identityʳ pcm₂ a₂))
        }
      ; comm = λ (a₁ , a₂) (b₁ , b₂) → cong₂ _,_ (⊗-comm pcm₁ a₁ b₁) (⊗-comm pcm₂ a₂ b₂)
      }
    ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive = λ { refl → ≤-refl pcm₁ , ≤-refl pcm₂ }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans pcm₁ h₁ h₁' , ≤-trans pcm₂ h₂ h₂'
      }
    ; isMonotone-⊕ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊕-mono-≤ pcm₁ h₁ h₁' , ⊕-mono-≤ pcm₂ h₂ h₂'
      }
    ; isMonotone-⊗ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊗-mono-≤ pcm₁ h₁ h₁' , ⊗-mono-≤ pcm₂ h₂ h₂'
      }
    }
  }
  where open ParCostMonoid

ℕ²-ParCostMonoid : ParCostMonoid
ℕ²-ParCostMonoid = combineParCostMonoids ℕ-Work-ParCostMonoid ℕ-Span-ParCostMonoid
