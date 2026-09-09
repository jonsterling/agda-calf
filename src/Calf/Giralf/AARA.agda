module Calf.Giralf.AARA where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Empty
open import Calf.Value.List
open import Calf.Value.Product
open import Calf.Value.Sum
open import Calf.Value.Unit as Unit
open import Calf.Computation
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Copower
open import Calf.Computation.Credit
open import Calf.Computation.Empty
open import Calf.Computation.Free
open import Calf.Computation.Potential
open import Calf.Computation.Sum
open import Calf.Computation.Tensor as Tensor
open import Calf.Giralf

data AARA : 𝒱₁ where
  Fᴬ : 𝒱 → AARA
  ⊤ᴬ : AARA
  _⊗ᴬ_ : AARA → AARA → AARA
  0ᴬ : AARA
  _+ᴬ_ : AARA → AARA → AARA
  ▷ᴬ_ : ℂ → AARA → AARA
  CList₁ᴬ : ℂ → 𝒱₌ → AARA
  CList₂ᴬ : ℂ → ℂ → 𝒱₌ → AARA

⟦_⟧ : AARA → 𝒱
⟦ Fᴬ X ⟧ = X
⟦ ⊤ᴬ ⟧ = 1ᵛ
⟦ A ⊗ᴬ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ 0ᴬ ⟧ = ⊥
⟦ A +ᴬ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ (▷ᴬ c) A ⟧ = ⟦ A ⟧
⟦ CList₁ᴬ c X₌ ⟧ = List ⟨ X₌ ⟩
⟦ CList₂ᴬ c₁ c₂ X₌ ⟧ = List ⟨ X₌ ⟩

Φ : (A : AARA) → ⟦ A ⟧ → ℂ
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
ι (Fᴬ X) = F X
ι ⊤ᴬ = ⊤
ι (A ⊗ᴬ B) = ι A ⊗ ι B
ι 0ᴬ = 0ᶜ
ι (A +ᴬ B) = ι A +ᶜ ι B
ι ((▷ᴬ c) A) = ▷[ c ] ι A
ι (CList₁ᴬ c X₌) = CList₁ c X₌
ι (CList₂ᴬ c₁ c₂ X₌) = CList₂ c₁ c₂ X₌

aara-potential : (A : AARA) → ι A ≡ Potential (Φ A)
aara-potential A = lemma A ∙ sym (Potential-credit (Φ A))
  where
    isSet⟦_⟧ : (A : AARA)→ isSet ⟦ A ⟧
    isSet⟦ Fᴬ X ⟧ = {!   !}
    isSet⟦ ⊤ᴬ ⟧ = {!   !}
    isSet⟦ A ⊗ᴬ B ⟧ = {!   !}
    isSet⟦ 0ᴬ ⟧ = {!   !}
    isSet⟦ A +ᴬ B ⟧ = {!   !}
    isSet⟦ (▷ᴬ c) B ⟧ = {!   !}
    isSet⟦ CList₁ᴬ c X₌ ⟧ = {!   !}
    isSet⟦ CList₂ᴬ c₁ c₂ X₌ ⟧ = {!   !}

    isDiscrete⟦_⟧ : (A : AARA)→ isDiscrete ⟦ A ⟧
    isDiscrete⟦ Fᴬ X ⟧ = {!   !}
    isDiscrete⟦ ⊤ᴬ ⟧ = {!   !}
    isDiscrete⟦ A ⊗ᴬ B ⟧ = {!   !}
    isDiscrete⟦ 0ᴬ ⟧ = {!   !}
    isDiscrete⟦ A +ᴬ B ⟧ = {!   !}
    isDiscrete⟦ (▷ᴬ c) B ⟧ = {!   !}
    isDiscrete⟦ CList₁ᴬ c X₌ ⟧ = {!   !}
    isDiscrete⟦ CList₂ᴬ c₁ c₂ X₌ ⟧ = {!   !}

    ⟦_⟧₌ : AARA → 𝒱₌
    ⟦ A ⟧₌ = ⟦ A ⟧ , isSet⟦ A ⟧ , isDiscrete⟦ A ⟧

    lemma : (A : AARA) → ι A ≡ [ a ∈ ⟦ A ⟧₌ ] ⋊ ▷[ Φ A a ] Tensor.⊤
    lemma (Fᴬ X) = {!   !}
    lemma ⊤ᴬ = {!   !} ∙ cong (Σᶜ ⟦ ⊤ᴬ ⟧₌) (funExt λ _ → sym ▷-0)
    lemma (A ⊗ᴬ B) = {!   !}
    lemma 0ᴬ = {!   !}
    lemma (A +ᴬ B) = {!   !}
    lemma ((▷ᴬ c) A) = {!   !}
    lemma (CList₁ᴬ c X₌) = {!   !}
    lemma (CList₂ᴬ c₁ c₂ X₌) = {!   !}
