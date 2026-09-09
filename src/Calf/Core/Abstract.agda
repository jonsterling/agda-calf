module Calf.Core.Abstract where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

opaque
  ABS : hProp ℓ-zero
  ABS = Unit , isPropUnit
