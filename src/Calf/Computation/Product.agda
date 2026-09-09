module Calf.Computation.Product where

open import Calf.Value
open import Calf.Computation

open import Calf.Value.Product public

infixr 2 _×ᶜ_

_×ᶜ_ : 𝒞 → 𝒞 → 𝒞
(A ×ᶜ B) .U = A .U × B .U
(A ×ᶜ B) .is-preorder = isPreorder× (A .is-preorder) (B .is-preorder)
(A ×ᶜ B) .charge c e .fst = A .charge c (e .fst)
(A ×ᶜ B) .charge c e .snd = B .charge c (e .snd)
(A ×ᶜ B) .charge-0 {e} i .fst = A .charge-0 {e .fst} i
(A ×ᶜ B) .charge-0 {e} i .snd = B .charge-0 {e .snd} i
(A ×ᶜ B) .charge-+ {e} {c₁} {c₂} i .fst = A .charge-+ {e .fst} {c₁} {c₂} i
(A ×ᶜ B) .charge-+ {e} {c₁} {c₂} i .snd = B .charge-+ {e .snd} {c₁} {c₂} i

pairᶜ : (A ⊸ B) → (A ⊸ C) → (A ⊸ B ×ᶜ C)
pairᶜ f g .U a = f .U a , g .U a
pairᶜ f g .charge c a = cong₂ _,_ (f .charge c a) (g .charge c a)

proj₁ᶜ : A ×ᶜ B ⊸ A
proj₁ᶜ .U = fst
proj₁ᶜ .charge c a = refl

proj₂ᶜ : A ×ᶜ B ⊸ B
proj₂ᶜ .U = snd
proj₂ᶜ .charge c b = refl
