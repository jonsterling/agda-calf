{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Sequence.ArrayCostMonoid using (ArrayCostMonoid; read; write; alloc)
open import CalfMonad.CostMonad                using (CostMonad)

module CalfMonad.Sequence.Array ℓ ℓ′ ℓ″ (arrayCostMonoid : ArrayCostMonoid ℓ′ ℓ) (costMonad : CostMonad ℓ ℓ′ ℓ″ (ArrayCostMonoid.costMonoid arrayCostMonoid)) where

open ArrayCostMonoid arrayCostMonoid
open CostMonad costMonad

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

open import CalfMonad.Sequence.ArraySig ℓ′ ℓ″ monad

array : ARRAY
array = record
  { Array = Vec
  ; ArrayBuilder = λ A n S m → ∀ i → T (lookup m i) → A
  ; nth = λ {A} {n} as i → do
    let a = lookup as i
    step $ arrayStep $ read A n i a
    pure a
  ; empty = pure λ i p → ⊥-elim $ subst T (lookup∘tabulate _ i) p
  ; assign = λ {n} {A} i a → do
    step $ arrayStep $ write A n i a
    pure λ j p → a
  ; join = λ b₁ b₂ → pure λ i p → [ b₁ i , b₂ i ] $ Equivalence.to T-∨ ⟨$⟩ subst T (lookup∘tabulate _ i) p
  ; build = λ {A} {n} b → do
    step $ arrayStep $ alloc A n
    b ← b {⊥}
    pure $ tabulate λ i → b i $ subst T (sym $ lookup∘tabulate _ i) tt
  }
