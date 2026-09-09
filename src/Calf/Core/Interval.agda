module Calf.Core.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Relation.Binary.Definitions
  using (Antisymmetric; Maximum; Minimum; Reflexive; Transitive)

opaque
  𝟚 : Type
  𝟚 = Unit

  isSet𝟚 : isSet 𝟚
  isSet𝟚 = isSetUnit

  _≤𝟚_ : 𝟚 → 𝟚 → Type
  tt ≤𝟚 tt = Unit

  ≤𝟚-isProp : ∀ {i j} → isProp (i ≤𝟚 j)
  ≤𝟚-isProp = isContr→isProp isContrUnit

  ≤𝟚-refl : Reflexive _≤𝟚_
  ≤𝟚-refl = tt

  ≤𝟚-trans : Transitive _≤𝟚_
  ≤𝟚-trans _ _ = tt

  ≤𝟚-antisym : Antisymmetric _≡_ _≤𝟚_
  ≤𝟚-antisym = isContr→isProp isContrUnit

  0𝟚 1𝟚 : 𝟚
  0𝟚 = tt
  1𝟚 = tt

  0𝟚-minimum : Minimum _≤𝟚_ 0𝟚
  0𝟚-minimum _ = tt

  1𝟚-maximum : Maximum _≤𝟚_ 1𝟚
  1𝟚-maximum tt = tt
