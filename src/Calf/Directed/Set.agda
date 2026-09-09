module Calf.Directed.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.HITs.Nullification
open import Cubical.HITs.S1
open import Cubical.HITs.Truncation.Properties
  using (isSphereFilled→isOfHLevel; isOfHLevel→isSphereFilled)

private variable X : Type

open isPathSplitEquiv

isS¹Null≡isSet : isNull (const {B = Unit} S¹) X ≡ isSet X
isS¹Null≡isSet {X} = hPropExt isPropIsNull isPropIsSet to from
  where
    to : isNull (const {B = Unit} S¹) X → isSet X
    to nullX =
      isSphereFilled→isOfHLevel 1 λ f → nullX tt .sec .fst f , funExt⁻ (nullX tt .sec .snd f)

    from : isSet X → isNull (const {B = Unit} S¹) X
    from setX =
      SeparatedAndInjective→Null X
        (λ x y _ →
          fromIsEquiv _
            (isoToIsEquiv (isProp→Iso (setX x y) (isPropΠ λ _ → setX x y) const (_$ base))))
        (λ _ → (λ f → sphere-fill f .fst) , λ f → funExt (sphere-fill f .snd))
      where sphere-fill = isOfHLevel→isSphereFilled 1 setX
