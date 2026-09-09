module Calf.Computation.CList1 where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Free
open import Calf.Computation.Potential using (▷-Σᶜ)
open import Calf.Computation.Tensor

opaque
  CList₁ : ℂ → 𝒱₌ → 𝒞
  CList₁ c X₌ = [ l ∈ List₌ X₌ ] ⋊ ▷[ length l ⊙ c ] ⊤

  nil₁ : ∀ {c} → U (CList₁ c X₌)
  nil₁ = [] , subst U (sym ▷-0) 0ℂ

  cons₁ : ∀ {c} → ⟨ X₌ ⟩ → ▷[ c ] CList₁ c X₌ ⊸ CList₁ c X₌
  cons₁ {X} {c} x =
    transport (cong (_⊸ CList₁ c X) (sym (▷-Σᶜ c))) $
    Σᶜ-rec λ l → transport (cong (_⊸ CList₁ c X) ▷-+) (Σᶜ-in (x ∷ l))

  foldr₁ : ∀ {c} → U A → (⟨ X₌ ⟩ → ▷[ c ] A ⊸ A) → CList₁ c X₌ ⊸ A
  foldr₁ {A} {X} {c} e-nil e-cons = Σᶜ-rec go
    where
      go : (l : List ⟨ X ⟩) → ▷[ length l ⊙ c ] ⊤ ⊸ A
      go [] = ▷⊤-rec e-nil
      go (x ∷ l) = transport (cong (_⊸ A) (sym ▷-+)) (▷-map (go l) ⨾ᶜ e-cons x)

opaque
  unfolding CList₁

  CList₁-credit : CList₁ c X₌ ≡ ([ l ∈ List₌ X₌ ] ⋊ ▷[ length l ⊙ c ] ⊤)
  CList₁-credit = refl

  CList₁-open : ⟨ ABS ⟩ → CList₁ c X₌ ≃ᶜ F (List ⟨ X₌ ⟩)
  CList₁-open abs = {!   !}
