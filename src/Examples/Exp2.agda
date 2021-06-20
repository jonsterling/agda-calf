{-# OPTIONS --prop --rewriting #-}

module Examples.Exp2 where

open import Calf.CostMonoid using (ParCostMonoid)
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf.Prelude
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool costMonoid
open import Calf.Types.Nat costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Nat as Nat
open import Data.Nat.Properties as N using (module ≤-Reasoning)

exp₂-slow : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
exp₂-slow ℕ.zero = ret (ℕ.suc ℕ.zero)
exp₂-slow (ℕ.suc n) = bind (F (U (meta ℕ))) (exp₂-slow n & exp₂-slow n) λ (r₁ , r₂) → ret (r₁ Nat.+ r₂)

exp₂-fast : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
exp₂-fast ℕ.zero = ret (ℕ.suc ℕ.zero)
exp₂-fast (ℕ.suc n) = bind (F (U (meta ℕ))) (exp₂-fast n) λ r → ret (r Nat.+ r)
