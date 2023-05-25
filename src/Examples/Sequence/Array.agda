{-# OPTIONS --cubical-compatible --prop --rewriting #-}

open import Examples.Sequence.ArrayCostMonoid

module Examples.Sequence.Array (arrayCostMonoid : ArrayCostMonoid) where

open ArrayCostMonoid arrayCostMonoid

open import Examples.Sequence.ArraySig

open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Calf.Types.Vec

open import Data.Bool                             using (T)
open import Data.Bool.Properties                  using (T-∨)
open import Data.Empty                            using (⊥-elim)
open import Data.Sum                              using ([_,_])
open import Data.Vec                              using (lookup; tabulate)
open import Data.Vec.Properties                   using (lookup∘tabulate)
open import Function                              using (_$_)
open import Function.Equality                     using (_⟨$⟩_)
open import Function.Equivalence                  using (Equivalence)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open ARRAY

Array : ARRAY

array  Array       = vec
update Array A n m = U $ meta ∀ i → T (lookup m i) → val A

nth Array {A} n as i =
  let a = lookup as i in
  step (F A) (arrayCost $ read A n i a) $
  ret a

nil Array n =
  ret λ i p → ⊥-elim $ subst T (lookup∘tabulate _ i) p

assign Array {A} n i a =
  step (F _) (arrayCost $ write A n i a) $
  ret λ j p → a

join Array n m₁ u₁ m₂ u₂ =
  ret λ i p → [ u₁ i , u₂ i ] $ Equivalence.to T-∨ ⟨$⟩ subst T (lookup∘tabulate _ i) p

mk Array {A} n u =
  step (F _) (arrayCost $ alloc A n) $
  bind (F _) u λ u →
  ret $ tabulate λ i → u i $ subst T (sym $ lookup∘tabulate _ i) _
