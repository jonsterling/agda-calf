module Calf.Value.List where

open import Cubical.Data.List using (isOfHLevelList)
open import Cubical.Data.Nat

open import Calf.Value
open import Calf.Value.Nat
open import Calf.Value.Product
open import Calf.Value.Sigma
open import Calf.Value.Unit

open import Cubical.Data.List public
  using (List; []; _∷_; foldr; _++_; [_]; length)
  renaming (rev to reverse)

isSetList : isSet X → isSet (List X)
isSetList = isOfHLevelList 0

module _ {X : 𝒱} where
  private
    Vec : ℕ → 𝒱
    Vec n = iter n (X ×_) Unit

    fwd : Σ ℕ Vec → List X
    fwd (zero , tt) = []
    fwd (suc n , x , xs) = x ∷ fwd (n , xs)

    bwd : List X → Σ ℕ Vec
    bwd [] = 0 , tt
    bwd (x ∷ xs) = let (n , v) = bwd xs in suc n , x , v

    fwd-bwd : section fwd bwd
    fwd-bwd [] = refl
    fwd-bwd (x ∷ l) = cong (x ∷_) (fwd-bwd l)

  isPreorderList : isPreorder X → isPreorder (List X)
  isPreorderList isPreorderX = isLocalRetract bwd fwd fwd-bwd (isPreorderΣ ℕ₌ isPreorderVec)
    where
      isPreorderVec : (n : ℕ) → isPreorder (Vec n)
      isPreorderVec zero = isPreorder1ᵛ
      isPreorderVec (suc n) = isPreorder× isPreorderX (isPreorderVec n)

  isDiscreteList : isDiscrete X → isDiscrete (List X)
  isDiscreteList isDiscreteX = isLocalRetract bwd fwd fwd-bwd (isDiscreteΣ isDiscreteℕ isDiscreteVec)
    where
      isDiscreteVec : (n : ℕ) → isDiscrete (Vec n)
      isDiscreteVec zero = isDiscrete1ᵛ
      isDiscreteVec (suc n) = isDiscrete× isDiscreteX (isDiscreteVec n)

List₌ : 𝒱₌ → 𝒱₌
List₌ X = List ⟨ X ⟩ , isSetList (str X .fst) , isDiscreteList (str X .snd)
