module Calf.Computation.Pullback where

open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation

open import Calf.Value.Sigma public

Pullback : ∀ {A B C} → (f : A ⊸ C) (g : B ⊸ C) → 𝒞
Pullback {A} {B} {C} f g .U =
  Σ[ (a , b) ∈ U A × U B ] f .U a ≡ g .U b
Pullback {A} {B} {C} f g .is-preorder =
  isLocalPullback
    (A .is-preorder) (B .is-preorder) (C .is-preorder)
    (f .U) (g .U)
Pullback {A} {B} {C} f g .charge c ((a , b) , p) =
  (A .charge c a , B .charge c b) ,
  f .charge c a ∙ cong (C .charge c) p ∙ sym (g .charge c b)
Pullback {A} {B} {C} f g .charge-0 =
  ΣPathP (ΣPathP (A .charge-0 , B .charge-0) , isProp→PathP (λ i → is-set C _ _) _ _)
Pullback {A} {B} {C} f g .charge-+ =
  ΣPathP (ΣPathP (A .charge-+ , B .charge-+) , isProp→PathP (λ i → is-set C _ _) _ _)
