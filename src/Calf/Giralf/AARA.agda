module Calf.Giralf.AARA where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Empty
open import Calf.Value.List
open import Calf.Value.Product
open import Calf.Value.Sum
open import Calf.Value.Unit
open import Calf.Computation
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Empty
open import Calf.Computation.Free
open import Calf.Computation.Potential
open import Calf.Computation.Sum
open import Calf.Computation.Tensor
open import Calf.Giralf

data AARA : 𝒱₁ where
  Fᴬ : 𝒱₌ → AARA
  ⊤ᴬ : AARA
  _⊗ᴬ_ : AARA → AARA → AARA
  0ᴬ : AARA
  _+ᴬ_ : AARA → AARA → AARA
  ▷ᴬ_ : ℂ → AARA → AARA
  CList₁ᴬ : ℂ → 𝒱₌ → AARA
  CList₂ᴬ : ℂ → ℂ → 𝒱₌ → AARA

⟦_⟧ : AARA → 𝒱₌
⟦ Fᴬ X ⟧ = X
⟦ ⊤ᴬ ⟧ = 1ᵛ₌
⟦ A ⊗ᴬ B ⟧ = ⟦ A ⟧ ×₌ ⟦ B ⟧
⟦ 0ᴬ ⟧ = ⊥₌
⟦ A +ᴬ B ⟧ = ⟦ A ⟧ ⊎₌ ⟦ B ⟧
⟦ (▷ᴬ c) A ⟧ = ⟦ A ⟧
⟦ CList₁ᴬ c X₌ ⟧ = List₌ X₌
⟦ CList₂ᴬ c₁ c₂ X₌ ⟧ = List₌ X₌

Φ : (A : AARA) → ⟨ ⟦ A ⟧ ⟩ → ℂ
Φ (Fᴬ X) a = 0ℂ
Φ ⊤ᴬ a = 0ℂ
Φ (A ⊗ᴬ B) (a , b) = Φ A a +ℂ Φ B b
Φ 0ᴬ ()
Φ (A +ᴬ B) (inj₁ a) = Φ A a
Φ (A +ᴬ B) (inj₂ b) = Φ B b
Φ ((▷ᴬ c) A) a = c +ℂ Φ A a
Φ (CList₁ᴬ c X₌) l = length l ⊙ c
Φ (CList₂ᴬ c₁ c₂ X₌) l = CList₂-potential c₁ c₂ (length l)

ι : AARA → 𝒞
ι (Fᴬ X) = F ⟨ X ⟩
ι ⊤ᴬ = ⊤
ι (A ⊗ᴬ B) = ι A ⊗ ι B
ι 0ᴬ = 0ᶜ
ι (A +ᴬ B) = ι A +ᶜ ι B
ι ((▷ᴬ c) A) = ▷[ c ] ι A
ι (CList₁ᴬ c X₌) = CList₁ c X₌
ι (CList₂ᴬ c₁ c₂ X₌) = CList₂ c₁ c₂ X₌

aara-credit : (A : AARA) → ι A ≡ ([ a ∈ ⟦ A ⟧ ] ⋊ ▷[ Φ A a ] ⊤)
aara-credit (Fᴬ X) =
  F-Σᶜ X ∙ cong (Σᶜ X) (funExt λ _ → sym ▷-0)
aara-credit ⊤ᴬ =
  sym F-⊤ ∙ F-Σᶜ 1ᵛ₌ ∙ cong (Σᶜ 1ᵛ₌) (funExt λ _ → sym ▷-0)
aara-credit (A ⊗ᴬ B) =
    cong₂ _⊗_ (aara-credit A) (aara-credit B)
  ∙ Σᶜ-⊗
  ∙ cong (Σᶜ (⟦ A ⟧ ×₌ ⟦ B ⟧)) (funExt λ (a , b) → ▷-⊗ (Φ A a) (Φ B b))
aara-credit 0ᴬ =
  sym F-0 ∙ F-Σᶜ ⊥₌ ∙ cong (Σᶜ ⊥₌) (funExt λ ())
aara-credit (A +ᴬ B) =
    cong₂ _+ᶜ_ (aara-credit A) (aara-credit B)
  ∙ sym (Σᶜ-⊎ (λ z → ▷[ Φ (A +ᴬ B) z ] ⊤))
aara-credit ((▷ᴬ c) A) =
    cong ▷[ c ]_ (aara-credit A)
  ∙ ▷-Σᶜ c
  ∙ cong (Σᶜ ⟦ A ⟧) (funExt λ a → sym ▷-+)
aara-credit (CList₁ᴬ c X₌) = CList₁-credit
aara-credit (CList₂ᴬ c₁ c₂ X₌) = CList₂-credit

aara-potential : (A : AARA) → ι A ≡ Potential (Φ A)
aara-potential A = aara-credit A ∙ sym (Potential-credit (Φ A))
