module Examples.Giralf.Id where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Giralf

id₁ : CList₁ (1 +ℂ p) X₌ , 0ℂ ⊢ CList₁ p X₌
id₁ =
  foldr₁ᴳ
    nil₁ᴳ
    (λ x →
      spendᴳ 1 refl $
      cons₁ᴳ (+ℂ-identityʳ _) x $
      idᴳ refl
    )
    (idᴳ refl)

id₂ : ∀ p → CList₂ p 1 X₌ , 0ℂ ⊢ CList₁ p X₌
id₂ {X} p =
  foldr₂ᴳ
    (λ r → CList₁ r X)
    (λ r → nil₁ᴳ)
    (λ r x → cons₁ᴳ (+ℂ-identityʳ r) x id₁)
    (idᴳ refl)
