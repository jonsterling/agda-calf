module Calf.Computation.Lolli where

open import Cubical.Foundations.Univalence using (ua)

open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Tensor

infix 1 _⊸ᶜ_

_⊸ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ⊸ᶜ B) .U = A ⊸ B
(A ⊸ᶜ B) .is-preorder =
  isLocalRetract
    (λ f → f .U , funExt λ c → funExt λ a → f .charge c a)
    (λ (U , p) → record { U = U ; charge = λ c a → funExt⁻ (funExt⁻ p c) a })
    (λ _ → refl)
    (isLocalEqualizer
      (isLocalΠ λ _ → B .is-preorder)
      (isLocalΠ λ _ → isLocalΠ λ _ → B .is-preorder)
      (λ U c a → U (A .charge c a))
      (λ U c a → B .charge c (U a)))
(A ⊸ᶜ B) .charge c f .U a = B .charge c (f .U a)
(A ⊸ᶜ B) .charge c f .charge c' a =
  cong (B .charge c) (f .charge c' a)
  ∙ cong ((_$ f .U a) ∘ U) (chargeᶜ-comm {B} c' c)
(A ⊸ᶜ B) .charge-0 = ⊸-path refl refl (funExt λ a → B .charge-0)
(A ⊸ᶜ B) .charge-+ = ⊸-path refl refl (funExt λ a → B .charge-+)

opaque
  lolli-currying : (A ⊗ B ⊸ C) ≡ (A ⊸ (B ⊸ᶜ C))
  lolli-currying {A} {B} {C} =
    ua (isoToEquiv (iso curryᶜ uncurryᶜ curryᶜ-uncurryᶜ uncurryᶜ-curryᶜ))
    where
      curryᶜ : (A ⊗ B ⊸ C) → (A ⊸ (B ⊸ᶜ C))
      curryᶜ f .U a .U b = f .U (a ∥ b)
      curryᶜ f .U a .charge c b =
        cong (f .U) (sym (∥-slide {A = A} {B = B} c a b)) ∙ f .charge c (a ∥ b)
      curryᶜ f .charge c a =
        ⊸-path refl refl (funExt λ b → f .charge c (a ∥ b))

      uncurryᶜ : (A ⊸ (B ⊸ᶜ C)) → (A ⊗ B ⊸ C)
      uncurryᶜ f =
        ⊗-rec (λ a b → f .U a .U b)
          (λ c a b → cong (λ g → g .U b) (f .charge c a))
          (λ c a b → f .U a .charge c b)

      curryᶜ-uncurryᶜ : (f : A ⊸ (B ⊸ᶜ C)) → curryᶜ (uncurryᶜ f) ≡ f
      curryᶜ-uncurryᶜ f =
        ⊸-path refl refl (funExt λ a → ⊸-path refl refl refl)

      uncurryᶜ-curryᶜ : (f : A ⊗ B ⊸ C) → uncurryᶜ (curryᶜ f) ≡ f
      uncurryᶜ-curryᶜ f =
        ⊸-path refl refl
          (funExt (⊗₀-rec-unique (C .is-preorder) (uncurryᶜ (curryᶜ f) .U) (f .U) (λ a b → refl)))
