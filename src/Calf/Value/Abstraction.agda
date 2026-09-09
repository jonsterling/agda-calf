module Calf.Value.Abstraction where

open import Cubical.Foundations.Univalence using (ua-gluePath)

open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Glue as Glue hiding (square)
open import Calf.Value.Open as ◯

Abstraction : (X-⊤ X-abs : 𝒱) → (X-⊤ → X-abs) → 𝒱
Abstraction X-⊤ X-abs χ = Glue (● X-⊤) (◯ X-abs) (●.map (η◦ ∘ χ))

Abstraction-id : (X : 𝒱) → Abstraction X X id ≡ X
Abstraction-id X = glue-fracture-retract X

square
  : ∀ {X-⊤ X-abs Y-⊤ Y-abs}
  → (χ : X-⊤ → X-abs) (ψ : Y-⊤ → Y-abs)
  → (f-⊤ : X-⊤ → Y-⊤)
  → (f-abs : X-abs → Y-abs)
  → ((x-⊤ : X-⊤) → ψ (f-⊤ x-⊤) ≡ f-abs (χ x-⊤))
  → Abstraction X-⊤ X-abs χ → Abstraction Y-⊤ Y-abs ψ
square {X-⊤} {X-abs} {Y-⊤} {Y-abs} χ ψ f-⊤ f-abs f-coherence =
  Glue.square
    (●.map f-⊤)
    (◯.map f-abs)
    (●.elim (λ x• → ●-≡-isModal _ _) (λ x → cong (η• ∘ η◦) (f-coherence x)))

triangle : ∀ {X-⊤ X-abs} (χ : X-⊤ → X-abs) (x-⊤ : X-⊤) (x-abs : X-abs)
  → χ x-⊤ ≡ x-abs
  → Abstraction X-⊤ X-abs χ
triangle χ x-⊤ x-abs h = (η• x-⊤ , η◦ x-abs) , cong (η• ∘ η◦) h

triangle′ : ∀ {X-⊤ X-abs} (χ : X-⊤ → X-abs)
  → X-⊤ → Abstraction X-⊤ X-abs χ
triangle′ χ x = triangle χ x (χ x) refl

triangle′-id : PathP (λ i → X → Abstraction-id X i) (triangle′ id) id
triangle′-id = funExt λ x → symP (ua-gluePath (_ , fracture-isEquiv) refl)
