module Calf.Giralf.Nat where

open import Cubical.Data.Nat using (ℕ; _+_)

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
import Calf.Computation.CList2 as CList2
open import Calf.Computation.Credit
import Calf.Computation.Debit as Debit
open import Calf.Computation.Power
open import Calf.Computation.Product
open import Calf.Computation.Tensor
import Calf.Giralf as Giralf

_⋎₀ : ℕ → 𝒱
q ⋎₀ = 0 ≡ q

_⋎₂_ : ℕ → (ℕ × ℕ) → 𝒱
q ⋎₂ (q₁ , q₂) = q₁ + q₂ ≡ q

private
  ⋎₀ℂ : ∀ q → q ⋎₀ → Giralf._⋎₀ (# q)
  ⋎₀ℂ q split = cong ℕ→ℂ split

  ⋎₂ℂ : ∀ q q₁ q₂ → q ⋎₂ (q₁ , q₂) → Giralf._⋎₂_ (# q) (# q₁ , # q₂)
  ⋎₂ℂ q q₁ q₂ split = sym (ℕ→ℂ-+ q₁ q₂) ∙ cong ℕ→ℂ split

infix 1 _⊢_

opaque
  _⊢_ : 𝒞 × ℕ → 𝒞 → 𝒱
  (Δ , q) ⊢ A = Giralf._⊢_ (Δ , # q) A

  ◁[_]_ : ℕ → 𝒞 → 𝒞
  ◁[ p ] A = Debit.◁[ # p ] A

  CList₂ : ℕ → ℕ → 𝒱₌ → 𝒞
  CList₂ p₁ p₂ X = CList2.CList₂ (# p₁) (# p₂) X

cmpᴳ : 𝒞 → 𝒱
cmpᴳ = ⊤ , 0 ⊢_

substᵐᴳ : ∀ {Δ : 𝒞} {A : 𝒞} {q q' : ℕ} → q ≡ q' → Δ , q ⊢ A → Δ , q' ⊢ A
substᵐᴳ {Δ} {A} = subst (λ q → Δ , q ⊢ A)

subst2ᴳ : ∀ {Δ : 𝒞} {q p1 p1' p2 p2' : ℕ}
  → (A : ℕ → ℕ → 𝒞)
  → p1 ≡ p1' → p2 ≡ p2'
  → Δ , q ⊢ A p1 p2
  → Δ , q ⊢ A p1' p2'
subst2ᴳ {Δ} {q} A = subst2 λ p1 p2 → Δ , q ⊢ A p1 p2

opaque
  unfolding _⊢_ ◁[_]_ CList₂

  idᴳ : ∀ {A : 𝒞} {q : ℕ} → q ⋎₀ → A , q ⊢ A
  idᴳ {q = q} split = Giralf.idᴳ (⋎₀ℂ q split)

  spendᴳ : ∀ {Δ A : 𝒞} {q q' : ℕ} (p : ℕ) → q ⋎₂ (p , q') → Δ , q' ⊢ A → Δ , q ⊢ A
  spendᴳ {q = q} {q' = q'} p split = Giralf.spendᴳ (# p) (⋎₂ℂ q p q' split)

  getᴳ : ∀ {Δ A : 𝒞} {q q' : ℕ} (p : ℕ) → q' ⋎₂ (p , q) → Δ , q' ⊢ A → Δ , q ⊢ ◁[ p ] A
  getᴳ {q = q} {q' = q'} p split = Giralf.getᴳ (# p) (⋎₂ℂ q' p q split)

  payᴳ : ∀ {Δ A : 𝒞} {p q q' : ℕ} → q ⋎₂ (p , q') → Δ , q' ⊢ ◁[ p ] A → Δ , q ⊢ A
  payᴳ {p = p} {q = q} {q' = q'} split = Giralf.payᴳ (⋎₂ℂ q p q' split)

  nil₂ᴳ : ∀ {p₁ p₂ q : ℕ} → q ⋎₀ → ⊤ , q ⊢ CList₂ p₁ p₂ X₌
  nil₂ᴳ {q = q} split = Giralf.nil₂ᴳ (⋎₀ℂ q split)

  cons₂ᴳ : ∀ {Δ : 𝒞} {p₁ p₂ q q' : ℕ}
    → q ⋎₂ (p₁ , q')
    → ⟨ X₌ ⟩
    → Δ , q' ⊢ CList₂ (p₂ + p₁) p₂ X₌
    → Δ , q ⊢ CList₂ p₁ p₂ X₌
  cons₂ᴳ {X} {Δ} {p₁} {p₂} {q} {q'} split x e =
    Giralf.cons₂ᴳ (⋎₂ℂ q p₁ q' split) x
      (subst (λ c → Giralf._⊢_ (Δ , # q') (CList2.CList₂ c (# p₂) X)) (ℕ→ℂ-+ p₂ p₁) e)

  foldr₂ᴳ : ∀ {Δ : 𝒞} {p₁ p₂ q : ℕ}
    → (A : ℕ → 𝒞)
    → (∀ r → cmpᴳ (A r))
    → (∀ r → ⟨ X₌ ⟩ → A (p₂ + r) , r ⊢ A r)
    → Δ , q ⊢ CList₂ p₁ p₂ X₌
    → Δ , q ⊢ A p₁
  foldr₂ᴳ {X} {Δ} {p₁} {p₂} {q} A e-nil e-cons e =
    Giralf.foldr₂ᴳ A′ e-nil′ e-cons′ e ⨾ᶜ Πᶜ-app {C = λ (n , _) → A n} (p₁ , refl)
    where
      A′ : ℂ → 𝒞
      A′ c = Πᶜ (Σ[ n ∈ ℕ ] (# n) ≡ c) (λ (n , _) → A n)

      e-nil′ : ∀ c → Giralf.cmpᴳ (A′ c)
      e-nil′ c = Πᶜ-lam {C = λ (n , _) → A n} λ (n , _) → e-nil n

      e-cons′ : ∀ c → ⟨ X ⟩ → Giralf._⊢_ (A′ (# p₂ +ℂ c) , c) (A′ c)
      e-cons′ c x =
        Πᶜ-lam {C = λ (n , _) → A n} λ (n , n≡c) →
          ▷-map (Πᶜ-app {C = λ (n , _) → A n} (p₂ + n , ℕ→ℂ-+ p₂ n ∙ cong (# p₂ +ℂ_) n≡c))
          ⨾ᶜ subst (λ c → ▷[ c ] A (p₂ + n) ⊸ A n) n≡c (e-cons n x)

  pairᴳ : ∀ {Δ A B : 𝒞} {q : ℕ} → Δ , q ⊢ A → Δ , q ⊢ B → Δ , q ⊢ A ×ᶜ B
  pairᴳ = Giralf.pairᴳ

  proj₁ᴳ : ∀ {Δ A B : 𝒞} {q : ℕ} → Δ , q ⊢ A ×ᶜ B → Δ , q ⊢ A
  proj₁ᴳ {B = B} = Giralf.proj₁ᴳ {B = B}

  proj₂ᴳ : ∀ {Δ A B : 𝒞} {q : ℕ} → Δ , q ⊢ A ×ᶜ B → Δ , q ⊢ B
  proj₂ᴳ {A = A} = Giralf.proj₂ᴳ {A = A}

  powlamᴳ : ∀ {Δ A : 𝒞} {X : 𝒱} {q : ℕ} → (X → Δ , q ⊢ A) → Δ , q ⊢ X ⇀ A
  powlamᴳ {X = X} = Giralf.powlamᴳ {X = X}

  powappᴳ : ∀ {Δ A : 𝒞} {X : 𝒱} {q : ℕ} → X → Δ , q ⊢ X ⇀ A → Δ , q ⊢ A
  powappᴳ {X = X} = Giralf.powappᴳ {X = X}
