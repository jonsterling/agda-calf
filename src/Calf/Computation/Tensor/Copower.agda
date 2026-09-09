module Calf.Computation.Tensor.Copower where

open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation
open import Calf.Computation.Copower

open import Calf.Computation.Tensor.Base

opaque
  Σᶜ-⊗ : {A : ⟨ X₌ ⟩ → 𝒞} {B : ⟨ Y₌ ⟩ → 𝒞}
    → (Σᶜ₌ X₌ A ⊗ Σᶜ₌ Y₌ B) ≡ Σᶜ₌ (X₌ ×₌ Y₌) (λ (x , y) → A x ⊗ B y)
  Σᶜ-⊗ {X₌} {Y₌} {A} {B} = conservativity fwd (isoToIsEquiv (iso (fwd .U) (bwd .U) sect retr))
    where
      fwd : (Σᶜ₌ X₌ A ⊗ Σᶜ₌ Y₌ B) ⊸ Σᶜ₌ (X₌ ×₌ Y₌) (λ (x , y) → A x ⊗ B y)
      fwd =
        ⊗-rec (λ (x , a) (y , b) → (x , y) , (a ∥ b))
          (λ c (x , a) (y , b) → refl)
          (λ c (x , a) (y , b) → cong ((x , y) ,_) (sym (∥-slide c a b)))

      bwd : Σᶜ₌ (X₌ ×₌ Y₌) (λ (x , y) → A x ⊗ B y) ⊸ (Σᶜ₌ X₌ A ⊗ Σᶜ₌ Y₌ B)
      bwd =
        Σᶜ-rec λ (x , y) →
          ⊗-rec (λ a b → (x , a) ∥ (y , b))
            (λ c a b → refl)
            (λ c a b → sym (∥-slide c (x , a) (y , b)))

      sect : ∀ w → fwd .U (bwd .U w) ≡ w
      sect ((x , y) , t) =
        ⊗₀-rec-unique (Σᶜ₌ (X₌ ×₌ Y₌) (λ (x , y) → A x ⊗ B y) .is-preorder)
          (λ t → fwd .U (bwd .U ((x , y) , t)))
          ((x , y) ,_)
          (λ a b → refl)
          t

      retr : ∀ w → bwd .U (fwd .U w) ≡ w
      retr =
        ⊗₀-rec-unique isPreorderᴾ
          (λ w → bwd .U (fwd .U w))
          (λ w → w)
          (λ (x , a) (y , b) → refl)
