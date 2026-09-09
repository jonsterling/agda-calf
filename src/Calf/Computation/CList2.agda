module Calf.Computation.CList2 where

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Free
open import Calf.Computation.Potential using (▷-Σᶜ)
open import Calf.Computation.Tensor

CList₂-potential : ℂ → ℂ → ℕ → ℂ
CList₂-potential c-lin c-quad zero = 0ℂ
CList₂-potential c-lin c-quad (suc n) = c-lin +ℂ CList₂-potential (c-quad +ℂ c-lin) c-quad n

opaque
  CList₂ : ℂ → ℂ → 𝒱₌ → 𝒞
  CList₂ c-lin c-quad X₌ = [ l ∈ List₌ X₌ ] ⋊ ▷[ CList₂-potential c-lin c-quad (length l) ] ⊤

  nil₂ : ∀ {c-lin c-quad} → U (CList₂ c-lin c-quad X₌)
  nil₂ = [] , subst U (sym ▷-0) 0ℂ

  cons₂ : ∀ {c-lin c-quad}
    → ⟨ X₌ ⟩ → ▷[ c-lin ] CList₂ (c-quad +ℂ c-lin) c-quad X₌ ⊸ CList₂ c-lin c-quad X₌
  cons₂ {X} {c-lin} {c-quad} x =
    transport (cong (_⊸ CList₂ c-lin c-quad X) (sym (▷-Σᶜ c-lin))) $
    Σᶜ-rec λ l → transport (cong (_⊸ CList₂ c-lin c-quad X) ▷-+) (Σᶜ-in (x ∷ l))

  foldr₂ : ∀ {c-lin c-quad} (A : ℂ → 𝒞)
    → (∀ c → U (A c))
    → (∀ c → ⟨ X₌ ⟩ → ▷[ c ] A (c-quad +ℂ c) ⊸ A c)
    → CList₂ c-lin c-quad X₌ ⊸ A c-lin
  foldr₂ {X} {c-lin} {c-quad} A e-nil e-cons = Σᶜ-rec (λ l → go l c-lin)
    where
      go : (l : List ⟨ X ⟩) (c : ℂ) → ▷[ CList₂-potential c c-quad (length l) ] ⊤ ⊸ A c
      go [] c = ▷⊤-rec (e-nil c)
      go (x ∷ l) c =
        transport (cong (_⊸ A c) (sym ▷-+)) (▷-map (go l (c-quad +ℂ c)) ⨾ᶜ e-cons c x)

opaque
  unfolding CList₂

  CList₂-credit : CList₂ c₁ c₂ X₌ ≡ ([ l ∈ List₌ X₌ ] ⋊ ▷[ CList₂-potential c₁ c₂ (length l) ] ⊤)
  CList₂-credit = refl

  CList₂-open : ⟨ ABS ⟩ → CList₂ c₁ c₂ X₌ ≃ᶜ F (List ⟨ X₌ ⟩)
  CList₂-open abs = {!   !}
