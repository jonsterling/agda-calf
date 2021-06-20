{-# OPTIONS --prop --rewriting #-}

module Examples.Exp2 where

open import Calf.CostMonoid using (ParCostMonoid)
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid using (costMonoid)

open import Calf.Prelude
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Nat as Nat
open import Data.Nat.Properties as N using (module ≤-Reasoning)

exp₂-slow : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
exp₂-slow zero = ret (suc zero)
exp₂-slow (suc n) = bind (F (U (meta ℕ))) (exp₂-slow n & exp₂-slow n) λ (r₁ , r₂) →
  step' (F (U (meta ℕ))) (1 , 1) (ret (r₁ Nat.+ r₂))

exp₂-fast : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
exp₂-fast zero = ret (suc zero)
exp₂-fast (suc n) = bind (F (U (meta ℕ))) (exp₂-fast n) λ r →
  step' (F (U (meta ℕ))) (1 , 1) (ret (r Nat.+ r))
