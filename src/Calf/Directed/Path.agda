module Calf.Directed.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Definitions using (Reflexive)

open import Calf.Core.Interval

module _ {X : Type} where

  infix 4 _⊑_
  _⊑_ : X → X → Type
  x ⊑ x' = Σ[ p ∈ (𝟚 → X) ] ((p 0𝟚 ≡ x) × (p 1𝟚 ≡ x'))

  path : {x x' : X} → x ⊑ x' → 𝟚 → X
  path e = e .fst

  path₀ : {x x' : X} (e : x ⊑ x') → path e 0𝟚 ≡ x
  path₀ e = e .snd .fst

  path₁ : {x x' : X} (e : x ⊑ x') → path e 1𝟚 ≡ x'
  path₁ e = e .snd .snd

  ⊑-reflexive : _≡_ ⇒ _⊑_
  ⊑-reflexive {x = x} x≡x' = (λ _ → x) , refl , x≡x'

  ⊑-refl : Reflexive _⊑_
  ⊑-refl = ⊑-reflexive refl

  ≡∙⊑ : {x y z : X} → x ≡ y → y ⊑ z → x ⊑ z
  ≡∙⊑ h e = path e , path₀ e ∙ sym h , path₁ e

  ⊑∙≡ : {x y z : X} → x ⊑ y → y ≡ z → x ⊑ z
  ⊑∙≡ e h = path e , path₀ e , path₁ e ∙ h

private variable X Y : Type

⊑-mono : (f : X → Y) {x x' : X} → x ⊑ x' → f x ⊑ f x'
⊑-mono f e = f ∘ path e , cong f (path₀ e) , cong f (path₁ e)

⊑-funext : {Y : X → Type}
  → {f f' : (x : X) → Y x}
  → ((x : X) → f x ⊑ f' x)
  → f ⊑ f'
⊑-funext pointwise =
    (λ 𝕚 x → path (pointwise x) 𝕚)
  , funExt (λ x → path₀ (pointwise x))
  , funExt (λ x → path₁ (pointwise x))

isContr⊑ : isContr X → {x x' : X} → isContr (x ⊑ x')
isContr⊑ isContrX =
  isContrΣ
    (isContrΠ (const isContrX))
    (λ _ →
      isContrΣ
        (isContr→isContrPath isContrX _ _)
        (const (isContr→isContrPath isContrX _ _)))
