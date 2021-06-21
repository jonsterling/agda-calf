{-# OPTIONS --prop --rewriting #-}

module Examples.Exp2 where

open import Calf.CostMonoid using (ParCostMonoid)
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid renaming (zero to 𝟘; _+_ to ⊕)

open import Calf.Prelude
open import Calf.ParMetalanguage parCostMonoid
open import Calf.PhaseDistinction costMonoid
open import Calf.Types.Bool costMonoid

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Nat as Nat
open import Data.Nat.Properties as N using (module ≤-Reasoning)

Correct : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ))) → Set
Correct exp₂ = (n : ℕ) → ◯ (exp₂ n ≡ ret (2 ^ n))

exp₂-slow : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
exp₂-slow zero = ret (suc zero)
exp₂-slow (suc n) = bind (F (U (meta ℕ))) (exp₂-slow n & exp₂-slow n) λ (r₁ , r₂) →
  step' (F (U (meta ℕ))) (1 , 1) (ret (r₁ + r₂))

lemma/2^suc : ∀ n → 2 ^ n + 2 ^ n ≡ 2 ^ suc n
lemma/2^suc n =
  begin
    2 ^ n + 2 ^ n
  ≡˘⟨ Eq.cong ((2 ^ n) +_) (N.*-identityˡ (2 ^ n)) ⟩
    2 ^ n + (2 ^ n + 0)
  ≡⟨⟩
    2 ^ n + (2 ^ n + 0 * (2 ^ n))
  ≡⟨⟩
    2 * (2 ^ n)
  ≡⟨⟩
    2 ^ suc n
  ∎
    where open ≡-Reasoning

exp₂-slow/correct : Correct exp₂-slow
exp₂-slow/correct zero    u = refl
exp₂-slow/correct (suc n) u =
  begin
    exp₂-slow (suc n)
  ≡⟨⟩
    (bind (F (U (meta ℕ))) (exp₂-slow n & exp₂-slow n) λ (r₁ , r₂) →
      step' (F (U (meta ℕ))) (1 , 1) (ret (r₁ + r₂)))
  ≡⟨ Eq.cong (bind (F (U (meta ℕ))) (exp₂-slow n & exp₂-slow n)) (funext (λ (r₁ , r₂) → step'/ext (F (U (meta ℕ))) _ (1 , 1) u)) ⟩
    (bind (F (U (meta ℕ))) (exp₂-slow n & exp₂-slow n) λ (r₁ , r₂) →
      ret (r₁ + r₂))
  ≡⟨ Eq.cong (λ e → bind (F (U (meta ℕ))) (e & e) _) (exp₂-slow/correct n u) ⟩
    (bind (F (U (meta ℕ))) (ret {U (meta ℕ)} (2 ^ n) & ret {U (meta ℕ)} (2 ^ n)) λ (r₁ , r₂) →
      ret (r₁ + r₂))
  ≡⟨ bind/par {p₁ = 𝟘} {p₂ = 𝟘} ⟩
    step' (F (U (meta ℕ))) (𝟘 ⊗ 𝟘) (ret (2 ^ n + 2 ^ n))
  ≡⟨⟩
    ret (2 ^ n + 2 ^ n)
  ≡⟨ Eq.cong ret (lemma/2^suc n) ⟩
    ret (2 ^ suc n)
  ∎
    where open ≡-Reasoning

exp₂-fast : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
exp₂-fast zero = ret (suc zero)
exp₂-fast (suc n) = bind (F (U (meta ℕ))) (exp₂-fast n) λ r →
  step' (F (U (meta ℕ))) (1 , 1) (ret (r + r))

exp₂-fast/correct : Correct exp₂-fast
exp₂-fast/correct zero    u = refl
exp₂-fast/correct (suc n) u =
  begin
    exp₂-fast (suc n)
  ≡⟨⟩
    (bind (F (U (meta ℕ))) (exp₂-fast n) λ r →
      step' (F (U (meta ℕ))) (1 , 1) (ret (r + r)))
  ≡⟨ Eq.cong (bind (F (U (meta ℕ))) (exp₂-fast n)) (funext (λ r → step'/ext (F (U (meta ℕ))) _ (1 , 1) u)) ⟩
    (bind (F (U (meta ℕ))) (exp₂-fast n) λ r →
      ret (r + r))
  ≡⟨ Eq.cong (λ e → bind (F (U (meta ℕ))) e _) (exp₂-fast/correct n u) ⟩
    (bind (F (U (meta ℕ))) (ret {U (meta ℕ)} (2 ^ n)) λ r →
      ret (r + r))
  ≡⟨⟩
    ret (2 ^ n + 2 ^ n)
  ≡⟨ Eq.cong ret (lemma/2^suc n) ⟩
    ret (2 ^ suc n)
  ∎
    where open ≡-Reasoning
