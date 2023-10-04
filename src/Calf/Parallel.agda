{-# OPTIONS --rewriting --allow-unsolved-metas #-}

-- The basic CBPV metalanguage, extended with parallelism.

open import Algebra.Cost

module Calf.Parallel (parCostMonoid : ParCostMonoid) where

open ParCostMonoid parCostMonoid

open import Calf.Prelude
open import Calf.CBPV
open import Calf.Directed
open import Calf.Step costMonoid

open import Calf.Data.Product
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.IsBounded costMonoid

open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate
  _∥_ : {A₁ A₂ : tp pos} → cmp (F A₁) → cmp (F A₂) → cmp (F (A₁ ×⁺ A₂))

  ∥/join : ∀ {A₁ A₂} {v₁ v₂ c₁ c₂} →
    step (F A₁) c₁ (ret v₁) ∥ step (F A₂) c₂ (ret v₂) ≡ step (F (A₁ ×⁺ A₂)) (c₁ ⊗ c₂) (ret (v₁ , v₂))

∥/join/𝟘 : ∀ {A₁ A₂} {v₁ : val A₁} {v₂ : val A₂} →
  ret {A₁} v₁ ∥ ret {A₂} v₂ ≡ ret (v₁ , v₂)
∥/join/𝟘 {A₁} {A₂} {v₁} {v₂} =
  let open ≡-Reasoning in
  begin
    ret v₁ ∥ ret v₂
  ≡⟨⟩
    step (F A₁) 𝟘 (ret v₁) ∥ step (F A₂) 𝟘 (ret v₂)
  ≡⟨ ∥/join {A₁} {A₂} {v₁} {v₂} {𝟘} {𝟘} ⟩
    step (F (Σ⁺ A₁ (λ _ → A₂))) (𝟘 ⊗ 𝟘) (ret (v₁ , v₂))
  ≡⟨ cong (λ c → step (F (Σ⁺ A₁ (λ _ → A₂))) c (ret (v₁ , v₂))) (⊗-identityˡ 𝟘) ⟩
    step (F (Σ⁺ A₁ (λ _ → A₂))) 𝟘 (ret (v₁ , v₂))
  ≡⟨⟩
    ret (v₁ , v₂)
  ∎
{-# REWRITE ∥/join ∥/join/𝟘 #-}

∥-mono-≲ : {A₁ A₂ : tp pos} {e₁ e₁' : cmp (F A₁)} {e₂ e₂' : cmp (F A₂)}
  → e₁ ≤⁻[ F A₁ ] e₁'
  → e₂ ≤⁻[ F A₂ ] e₂'
  → (e₁ ∥ e₂) ≤⁻[ F (A₁ ×⁺ A₂) ] (e₁' ∥ e₂')
∥-mono-≲ {A₁} {A₂} {e₁} {e₁'} {e₂} {e₂'} e₁≤e₁' e₂≤e₂' =
  ≤⁻-mono₂ _∥_ e₁≤e₁' e₂≤e₂'

boundg/par : {A₁ A₂ : tp pos} {e₁ : cmp (F A₁)} {e₂ : cmp (F A₂)} {b₁ b₂ : cmp cost} →
  IsBoundedG A₁ e₁ b₁ →
  IsBoundedG A₂ e₂ b₂ →
  IsBoundedG (Σ⁺ A₁ λ _ → A₂) (e₁ ∥ e₂) (bind cost (b₁ ∥ b₂) λ _ → ret triv)
boundg/par {A₁} {A₂} {e₁} {e₂} {b₁} {b₂} ib₁ ib₂ =
  let open ≤⁻-Reasoning cost in
  begin
    bind cost (e₁ ∥ e₂) (λ _ → ret triv)
  ≤⟨ {!   !} ⟩
    bind cost ((bind cost e₁ λ _ → ret triv) ∥ (bind cost e₂ λ _ → ret triv)) (λ _ → ret triv)
  ≤⟨ ≤⁻-mono (λ e → bind cost (e ∥ (bind cost e₂ λ _ → ret triv)) (λ _ → ret triv)) ib₁ ⟩
    bind cost (b₁ ∥ (bind cost e₂ λ _ → ret triv)) (λ _ → ret triv)
  ≤⟨ ≤⁻-mono (λ e → bind cost (b₁ ∥ e) (λ _ → ret triv)) ib₂ ⟩
    bind cost (b₁ ∥ b₂) (λ _ → ret triv)
  ∎

bound/par : {A₁ A₂ : tp pos} {e₁ : cmp (F A₁)} {e₂ : cmp (F A₂)} {c₁ c₂ : ℂ} →
  IsBounded A₁ e₁ c₁ →
  IsBounded A₂ e₂ c₂ →
  IsBounded (Σ⁺ A₁ λ _ → A₂) (e₁ ∥ e₂) (c₁ ⊗ c₂)
bound/par {A₁} {A₂} {e₁} {e₂} {c₁} {c₂} ib₁ ib₂ =
  boundg/par {A₁} {A₂} {e₁} {e₂} ib₁ ib₂
