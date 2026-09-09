module Examples.Id where

open import Calf.Core.Cost
open import Calf.Value hiding (id)
open import Calf.Value.BigO
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Free
open import Calf.Computation.Power
open import Calf.Computation.Tensor


module Easy where
  id : U (ℕ ⇀ F ℕ)
  id n = ret n

  id-bound : U (ℕ ⇀ F ℕ)
  id-bound n = ret n

  id-bounded : id ⊑ id-bound
  id-bounded = ⊑-funext λ _ → ⊑-refl

  id-correct : BEH → id ≡ ret
  id-correct beh = ⊑-BEH beh id-bounded

  id-asymptotic : given ℕ measured-via (λ n → n) , id ∈𝓞(λ n → 0)
  id-asymptotic =
    f[n]≤g[n]via λ n →
      ⊑∙≡
        (⊑-mono (λ e → bind {A = ⊤} (e n) (const 0ℂ)) id-bounded)
        bind-β

module Hard where
  id : U (ℕ ⇀ F ℕ)
  id zero = ret 0
  id (suc n) =
    chargeℕ (F _) 1 $
    bind[ F _ ] n' ← id n ⨾
    ret (suc n')

  id-bound : U (ℕ ⇀ F ℕ)
  id-bound n = chargeℕ (F _) n (ret n)

  id-bounded : id ⊑ id-bound
  id-bounded = ⊑-funext lemma
    where
      lemma : ∀ n → id n ⊑ id-bound n
      lemma zero = ⊑-refl
      lemma (suc n) =
        let open ⊑-Reasoning (F ℕ) in
        ⊑-mono (chargeℕ (F _) 1) $
        begin
          bind[ F _ ] n' ← id n ⨾ ret (suc n')
        ⊑⟨ ⊑-mono (λ e → bind[ F _ ] n' ← e ⨾ ret (suc n')) (lemma n) ⟩
          bind[ F _ ] n' ← id-bound n ⨾ ret (suc n')
        ≡ᴾ⟨ bind-chargeℕ-ret n ⟩
          chargeℕ (F _) n (ret (suc n))
        ∎ᴾ

  id-correct : BEH → id ≡ ret
  id-correct beh = ⊑-BEH beh id-bounded ∙ funExt (λ n → chargeℕ-BEH (F _) n beh)

  id-asymptotic : given ℕ measured-via (λ n → n) , id ∈𝓞(λ n → # n)
  id-asymptotic =
    f[n]≤g[n]via λ n →
      ⊑∙≡
        (⊑-mono (λ e → bind {A = ⊤} (e n) (const 0ℂ)) id-bounded)
        (bind-chargeℕ-ret n ∙ chargeℕ-charge ⊤ n ∙ +ℂ-identityʳ _)


easy≡hard : BEH → Easy.id ≡ Hard.id
easy≡hard beh = Easy.id-correct beh ∙ sym (Hard.id-correct beh)
