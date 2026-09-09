module Calf.Computation.Empty where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Copower

open import Calf.Value.Empty public

0ᶜ : 𝒞
0ᶜ .U = ∥ ⊥ ∥ᴾ
0ᶜ .is-preorder = isPreorderᴾ
0ᶜ .charge _ = rec isPreorderᴾ λ ()
0ᶜ .charge-0 {a} =
  rec-unique {X = ⊥} isPreorderᴾ (0ᶜ .charge 0ℂ) (λ x → x) (λ ()) a
0ᶜ .charge-+ {a} {c₁} {c₂} =
  cong (0ᶜ .charge c₁) (rec-unique {X = ⊥} isPreorderᴾ (λ x → x) (0ᶜ .charge c₂) (λ ()) a)

absurdᶜ : 0ᶜ ⊸ A
absurdᶜ {A} .U = rec (A .is-preorder) λ ()
absurdᶜ {A} .charge c = rec-unique (A .is-preorder) _ _ λ ()

Σᶜ-⊥ : ∀ {A} → Σᶜ₌ ⊥₌ A ≡ 0ᶜ
Σᶜ-⊥ =
  sym $
    conservativity
      absurdᶜ
      (isoToIsEquiv (iso _ (λ ()) (λ ()) (rec-unique isPreorderᴾ _ _ λ ())))
