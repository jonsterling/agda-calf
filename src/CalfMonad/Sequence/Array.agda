{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad
open import CalfMonad.Sequence.ArrayCostMonoid

module CalfMonad.Sequence.Array {ℓ ℓ′ ℓ″} {M : Set ℓ → Set ℓ′} {ℂ : Set ℓ″} {monad : Monad M} {costMonoid : CostMonoid ℂ} (costMonad : CostMonad monad costMonoid) (arrayCostMonoid : ArrayCostMonoid ℓ ℂ) where

open Monad monad
open CostMonad costMonad
open ArrayCostMonoid arrayCostMonoid

open import Data.Bool.Base       using (T)
open import Data.Bool.Properties using (T-∨)
open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Sum.Base        using ([_,_])
open import Data.Unit.Base       using (tt)
open import Data.Vec.Base        using (Vec; lookup; tabulate)
open import Data.Vec.Properties  using (lookup∘tabulate)
open import Function.Base        using (_$_)
open import Function.Equality    using (_⟨$⟩_)
open import Function.Equivalence using (Equivalence)
open import Relation.Binary.PropositionalEquality.Core using (subst; sym)

open import CalfMonad.Sequence.ArraySig M

open ARRAY

array : ARRAY

array .Array = Vec

array .ArrayBuilder A n S m = ∀ i → T (lookup m i) → A

array .nth {A} {n} as i = do
  step $ arrayStep $ read A n as i
  pure $ lookup as i

array .empty = pure λ i p → ⊥-elim $ subst T (lookup∘tabulate _ i) p

array .assign {n} {A} i a = do
  step $ arrayStep $ write A n i a
  pure λ j p → a

array .join b₁ b₂ = pure λ i p → [ b₁ i , b₂ i ] $ Equivalence.to T-∨ ⟨$⟩ subst T (lookup∘tabulate _ i) p

array .build {A} {n} b = do
  step $ arrayStep $ alloc A n
  b ← b {⊥}
  pure $ tabulate λ i → b i $ subst T (sym $ lookup∘tabulate _ i) tt
