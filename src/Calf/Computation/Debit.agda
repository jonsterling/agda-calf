module Calf.Computation.Debit where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Credit
open import Calf.Computation.Lolli
open import Calf.Computation.Tensor

opaque
  ◁[_]_ : ℂ → 𝒞 → 𝒞
  ◁[ c ] A = ▷[ c ] ⊤ ⊸ᶜ A

  ▷⊣◁ : ∀ {c} → (A ⊸ ◁[ c ] B) ≡ (▷[ c ] A ⊸ B)
  ▷⊣◁ {A} {B} {c} =
      (A ⊸ (◁[ c ] B))
    ≡⟨ refl ⟩
      (A ⊸ (▷[ c ] ⊤ ⊸ᶜ B))
    ≡⟨ sym lolli-currying ⟩
      ((A ⊗ (▷[ c ] ⊤)) ⊸ B)
    ≡⟨ cong (_⊸ B) (⊗-▷-distribʳ _) ⟩
      (▷[ c ] (A ⊗ ⊤) ⊸ B)
    ≡⟨ cong (λ C → (▷[ c ] C) ⊸ B) ⊗-identityʳ ⟩
      ((▷[ c ] A) ⊸ B)
    ∎

▷⊣◁-counit : ▷[ c ] ◁[ c ] A ⊸ A
▷⊣◁-counit = transport ▷⊣◁ idᶜ
