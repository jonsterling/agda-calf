module Calf.Computation.Sum where

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Copower

open import Calf.Value.Sum public

_+ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A +ᶜ B) .U = A .U ⊎ B .U
(A +ᶜ B) .is-preorder = isPreorder⊎ (A .is-preorder) (B .is-preorder)
(A +ᶜ B) .charge c (inj₁ a) = inj₁ (A .charge c a)
(A +ᶜ B) .charge c (inj₂ b) = inj₂ (B .charge c b)
(A +ᶜ B) .charge-0 {inj₁ a} = cong inj₁ (A .charge-0)
(A +ᶜ B) .charge-0 {inj₂ b} = cong inj₂ (B .charge-0)
(A +ᶜ B) .charge-+ {inj₁ a} = cong inj₁ (A .charge-+)
(A +ᶜ B) .charge-+ {inj₂ b} = cong inj₂ (B .charge-+)

inj₁ᶜ : A ⊸ A +ᶜ B
inj₁ᶜ .U = inj₁
inj₁ᶜ .charge _ _ = refl

inj₂ᶜ : B ⊸ A +ᶜ B
inj₂ᶜ .U = inj₂
inj₂ᶜ .charge _ _ = refl

opaque
  Σᶜ-⊎ : (A : ⟨ X₌ ⊎₌ Y₌ ⟩ → 𝒞)
    → Σᶜ (X₌ ⊎₌ Y₌) A ≡ (Σᶜ X₌ (A ∘ inj₁) +ᶜ Σᶜ Y₌ (A ∘ inj₂))
  Σᶜ-⊎ {X₌} {Y₌} A = conservativity fwd (isoToIsEquiv (iso (fwd .U) bwd sect retr))
    where
      fwd : Σᶜ (X₌ ⊎₌ Y₌) A ⊸ (Σᶜ X₌ (A ∘ inj₁) +ᶜ Σᶜ Y₌ (A ∘ inj₂))
      fwd .U (inj₁ x , a) = inj₁ (x , a)
      fwd .U (inj₂ y , a) = inj₂ (y , a)
      fwd .charge c (inj₁ x , a) = refl
      fwd .charge c (inj₂ y , a) = refl

      bwd : U (Σᶜ X₌ (A ∘ inj₁) +ᶜ Σᶜ Y₌ (A ∘ inj₂)) → U (Σᶜ (X₌ ⊎₌ Y₌) A)
      bwd (inj₁ (x , a)) = inj₁ x , a
      bwd (inj₂ (y , a)) = inj₂ y , a

      sect : ∀ w → fwd .U (bwd w) ≡ w
      sect (inj₁ _) = refl
      sect (inj₂ _) = refl

      retr : ∀ w → bwd (fwd .U w) ≡ w
      retr (inj₁ x , a) = refl
      retr (inj₂ y , a) = refl
