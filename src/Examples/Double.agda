module Examples.Double where

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Power

double : U (ℕ ⇀ F ℕ)
double zero = ret 0
double (suc n) =
  F _ .charge 1 $
  bind[ F ℕ ] n' ← double n ⨾
  ret (suc (suc n'))

opaque
  unfolding ℂ

  DOUBLE : ℕ → ℕ
  DOUBLE zero = 0
  DOUBLE (suc n) = suc (suc (DOUBLE n))

  double-bound : double ⊑[ ℕ ⇀ F ℕ ] (λ n → F _ .charge (# n) (ret (DOUBLE n)))
  double-bound = ⊑-funext lemma
    where
      lemma : ∀ n → double n ⊑[ F ℕ ] F _ .charge (# n) (ret (DOUBLE n))
      lemma zero = ⊑-reflexive (sym (F _ .charge-0))
      lemma (suc n) =
        let open ⊑-Reasoning (F ℕ) in
        begin
          double (suc n)
        ≡ᴾ⟨ refl ⟩
          F _ .charge 1 (bind (double n) (λ n' → ret (suc (suc n'))))
        ⊑⟨ ⊑-mono (λ e → F _ .charge 1 (bind e (λ n' → ret (suc (suc n'))))) (lemma n) ⟩
          F _ .charge 1 (bind (F _ .charge (# n) (ret (DOUBLE n))) (λ n' → ret (suc (suc n'))))
        ≡ᴾ⟨ cong (F _ .charge 1) bind-charge ⟩
          F _ .charge 1 (F _ .charge (# n) (bind {A = F _} (ret (DOUBLE n)) (λ n' → ret (suc (suc n')))))
        ≡ᴾ⟨ sym (F _ .charge-+) ⟩
          F _ .charge (# suc n) (bind {A = F _} (ret (DOUBLE n)) (λ n' → ret (suc (suc n'))))
        ≡ᴾ⟨ cong (F _ .charge (# suc n)) bind-β ⟩
          F _ .charge (# suc n) (ret (suc (suc (DOUBLE n))))
        ≡ᴾ⟨ refl ⟩
          F _ .charge (# suc n) (ret (DOUBLE (suc n)))
        ∎ᴾ

  double-bound-suc : double ⊑[ ℕ ⇀ F ℕ ] (λ n → F _ .charge (# suc n) (ret (DOUBLE n)))
  double-bound-suc =
    let open ⊑-Reasoning (ℕ ⇀ F ℕ) in
    begin
      double
    ⊑⟨ double-bound ⟩
      (λ n → F _ .charge (# n) (ret (DOUBLE n)))
    ⊑⟨ ⊑-funext (λ n → ⊑-mono (λ e → F _ .charge e (ret (DOUBLE n))) (≤⇒⊑ℂ {n} {suc n} (≤-suc ≤-refl))) ⟩
      (λ n → F _ .charge (# suc n) (ret (DOUBLE n)))
    ∎ᴾ
