module Calf.Directed.Thin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization

open import Calf.Core.Interval
open import Calf.Directed.Path

open import Cubical.HITs.Pushout public

private variable X Y : Type

𝕊 : Type → Type
𝕊 X = Pushout {A = X × Bool} (λ (x , b) → (x , (if b then 1𝟚 else 0𝟚))) snd

𝕊-map : (X → Y) → 𝕊 X → 𝕊 Y
𝕊-map f (inl (x , 𝕚)) = inl (f x , 𝕚)
𝕊-map f (inr b) = inr b
𝕊-map f (push (x , b) i) = push (f x , b) i

𝕊-cocone : Type → Type → Type
𝕊-cocone X Y = Σ (X × X) (λ (x , x') → Y → x ⊑ x')

open Iso

𝕊-elim : (Y : Type) → Iso (𝕊 Y → X) (𝕊-cocone X Y)
𝕊-elim Y .fun k =
  (k (inr false) , k (inr true)) , λ y →
      (λ 𝕚 → k (inl (y , 𝕚)))
    , cong k (push (y , false))
    , cong k (push (y , true))
𝕊-elim Y .inv (_ , q) (inl (y , 𝕚)) = path (q y) 𝕚
𝕊-elim Y .inv ((x , x') , q) (inr false) = x
𝕊-elim Y .inv ((x , x') , q) (inr true) = x'
𝕊-elim Y .inv (_ , q) (push (y , false) j) = path₀ (q y) j
𝕊-elim Y .inv (_ , q) (push (y , true) j) = path₁ (q y) j
𝕊-elim Y .rightInv (_ , q) = refl
𝕊-elim Y .leftInv k i (inl (y , 𝕚)) = k (inl (y , 𝕚))
𝕊-elim Y .leftInv k i (inr false) = k (inr false)
𝕊-elim Y .leftInv k i (inr true) = k (inr true)
𝕊-elim Y .leftInv k i (push (y , false) j) = k (push (y , false) j)
𝕊-elim Y .leftInv k i (push (y , true) j) = k (push (y , true) j)

𝕊-elim≃ : (Y : Type) → (𝕊 Y → X) ≃ 𝕊-cocone X Y
𝕊-elim≃ Y = isoToEquiv (𝕊-elim Y)

isBoundarySeparated : Type → Type
isBoundarySeparated = isLocal {A = Unit} (const (𝕊-map (terminal Bool)))

isThin : Type → Type
isThin X = (x x' : X) → isProp (x ⊑ x')

isThin→𝟚-injective : isThin X → {P Q : 𝟚 → X} → P 0𝟚 ≡ Q 0𝟚 → P 1𝟚 ≡ Q 1𝟚 → P ≡ Q
isThin→𝟚-injective isThinX {P} {Q} p q = cong path (isThinX _ _ (P , refl , refl) (Q , sym p , sym q))

isBoundarySeparated≡isThin : isBoundarySeparated X ≡ isThin X
isBoundarySeparated≡isThin {X} =
  hPropExt
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    (isPropΠ2 λ _ _ → isPropIsProp)
    isBoundarySeparated→isThin
    isThin→isBoundarySeparated
  where
    P Q : X × X → Type
    P (x , x') = Unit → x ⊑ x'
    Q (x , x') = Bool → x ⊑ x'

    φ : (xx' : X × X) → P xx' → Q xx'
    φ _ q _ = q tt

    isBoundarySeparated→isThin : isBoundarySeparated X → isThin X
    isBoundarySeparated→isThin isBoundarySeparatedX x x' p p' =
      sym (funExt⁻ secφ false) ∙ funExt⁻ secφ true
      where
        totalφ-isEquiv : isEquiv (λ ((xx' , q) : Σ (X × X) P) → xx' , φ xx' q)
        totalφ-isEquiv = equivIsEquiv $
          𝕊-cocone X Unit ≃⟨ invEquiv (𝕊-elim≃ Unit) ⟩
          (𝕊 Unit → X)    ≃⟨ _ , toIsEquiv _ (isBoundarySeparatedX tt) ⟩
          (𝕊 Bool → X)    ≃⟨ 𝕊-elim≃ Bool ⟩
          𝕊-cocone X Bool ■

        φ≃ : P (x , x') ≃ Q (x , x')
        φ≃ = φ (x , x') , fiberEquiv P Q φ totalφ-isEquiv (x , x')

        secφ : φ (x , x') (invEq φ≃ (if_then p' else p)) ≡ (if_then p' else p)
        secφ = secEq φ≃ (if_then p' else p)

    isThin→isBoundarySeparated : isThin X → isBoundarySeparated X
    isThin→isBoundarySeparated isThinX _ =
      fromIsEquiv _
        (isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (𝕊-elim≃ Bool)
          (equivIsEquiv (compEquiv (𝕊-elim≃ Unit) (_ , totalEquiv P Q φ φ-equiv))))
      where
        φ-equiv : (xx' : X × X) → isEquiv (φ xx')
        φ-equiv (x , x') = isoToIsEquiv
          (isProp→Iso (isPropΠ λ _ → isThinX x x') (isPropΠ λ _ → isThinX x x')
            (φ (x , x')) (λ q _ → q false))
