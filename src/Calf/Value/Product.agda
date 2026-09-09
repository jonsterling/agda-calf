module Calf.Value.Product where

open import Calf.Value

open import Cubical.Foundations.HLevels public
  using (isSet×)
open import Cubical.Data.Sigma public
  using (_×_; _,_)
  renaming (fst to proj₁; snd to proj₂)

opaque
  isDiscrete× : isDiscrete X → isDiscrete Y → isDiscrete (X × Y)
  isDiscrete× = isLocal×

  isPreorder× : isPreorder X → isPreorder Y → isPreorder (X × Y)
  isPreorder× = isLocal×

infixr 5 _×₌_

_×₌_ : 𝒱₌ → 𝒱₌ → 𝒱₌
X ×₌ Y =
  (⟨ X ⟩ × ⟨ Y ⟩) ,
  isSet× (str X .fst) (str Y .fst) ,
  isDiscrete× (str X .snd) (str Y .snd)
