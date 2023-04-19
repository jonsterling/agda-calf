{-# OPTIONS --prop --without-K --rewriting #-}

-- The basic CBPV metalanguage, extended with parallelism.

open import Calf.CostMonoid

module Calf.ParMetalanguage (parCostMonoid : ParCostMonoid) where

open ParCostMonoid parCostMonoid

open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid

open import Calf.Types.Bounded costMonoid

open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate
  _&_ : {A₁ A₂ : tp pos} → cmp (F A₁) → cmp (F A₂) → cmp (F (Σ++ A₁ (λ _ → A₂)))

  &/join : ∀ {A₁ A₂} {v₁ v₂ p₁ p₂} →
    step (F A₁) p₁ (ret v₁) & step (F A₂) p₂ (ret v₂) ≡ step (F (Σ++ A₁ λ _ → A₂)) (p₁ ⊗ p₂) (ret (v₁ , v₂))
  {-# REWRITE &/join #-}

  &-mono-≲ : {A₁ A₂ : tp pos} {e₁ e₁' : cmp (F A₁)} {e₂ e₂' : cmp (F A₂)}
    → _≲_ {F A₁} e₁ e₁'
    → _≲_ {F A₂} e₂ e₂'
    → _≲_ {F (Σ++ A₁ (λ _ → A₂))} (e₁ & e₂) (e₁' & e₂')

&/join/𝟘 : ∀ {A₁ A₂} {v₁ v₂} →
  ret v₁ & ret v₂ ≡ step (F (Σ++ A₁ λ _ → A₂)) (𝟘 ⊗ 𝟘) (ret (v₁ , v₂))
&/join/𝟘 = &/join {p₁ = 𝟘} {p₂ = 𝟘}
{-# REWRITE &/join/𝟘 #-}

bind/& : ∀ {A₁ A₂} {X} {v₁ v₂ f} (p₁ p₂ : ℂ) →
  bind {Σ++ A₁ λ _ → A₂} X (step (F A₁) p₁ (ret v₁) & step (F A₂) p₂ (ret v₂)) f ≡ step X (p₁ ⊗ p₂) (f (v₁ , v₂))
bind/& _ _ = refl

open import Calf.Types.Unit

bound/par : {A₁ A₂ : tp pos} {e₁ : cmp (F A₁)} {e₂ : cmp (F A₂)} {c₁ c₂ : ℂ} →
  IsBounded A₁ e₁ c₁ →
  IsBounded A₂ e₂ c₂ →
  IsBounded (Σ++ A₁ λ _ → A₂) (e₁ & e₂) (c₁ ⊗ c₂)
bound/par = {!   !}

-- bound/par {A₁} {A₂} {e₁} {e₂} {c₁} {c₂} ib₁ ib₂ result =
--   let open ≲-Reasoning (F unit) in
--   begin
--     bind (F unit) (e₁ & e₂) (λ _ → result)
--   ≡⟨⟩
--     bind (F unit)
--       ((bind (F A₁) e₁ ret) & (bind (F A₂) e₂ ret))
--       (λ _ → result)
--   ≡⟨ {!   !} ⟩
--     {!   !}
--   ≤⟨ bind-mono-≲ (&-mono-≲ (ib₁ (ret triv)) (ib₂ (ret triv))) (λ _ → ≲-refl {F unit} {result}) ⟩
--     bind (F unit)
--       (step (F unit) c₁ (ret triv) & step (F unit) c₂ (ret triv))
--       (λ _ → result)
--   ≡⟨⟩
--     step (F unit) (c₁ ⊗ c₂) result
--   ∎

-- bound/par {e₁ = e₁} {e₂} {c₁} {c₂} ib₁ ib₂ result =
--   let open ≲-Reasoning (F unit) in
--   begin
--     bind (F unit) (e₁ & e₂) (λ _ → result)
--   ≡⟨ {!   !} ⟩
--     bind (F unit)
--       ((bind (F unit) e₁ λ _ → ret triv) & (bind (F unit) e₂ λ _ → ret triv))
--       (λ _ → result)
--   ≤⟨ bind-mono-≲ (&-mono-≲ (ib₁ (ret triv)) (ib₂ (ret triv))) (λ _ → ≲-refl {F unit} {result}) ⟩
--     bind (F unit)
--       (step (F unit) c₁ (ret triv) & step (F unit) c₂ (ret triv))
--       (λ _ → result)
--   ≡⟨⟩
--     step (F unit) (c₁ ⊗ c₂) result
--   ∎

-- bound/par {e₁ = e₁} {e₂} {c₁} {c₂} ib₁ ib₂ result =
--   let open ≲-Reasoning (F unit) in
--   begin
--     bind (F unit) (e₁ & e₂) (λ _ → result)
--   ≡⟨ {! _&_ {unit} {unit} (ret triv) (ret triv)   !} ⟩
--     bind (F unit) (e₁ & e₂) (λ _ → bind (F unit) (_&_ {unit} {unit} (ret triv) (ret triv)) (λ _ → result))
--   ≡⟨ {!   !} ⟩
--     bind (F unit) ((bind (F unit) e₁ λ _ → ret triv) & (bind (F unit) e₂ λ _ → ret triv)) (λ _ → result)
--   ≤⟨ bind-mono-≲ (&-mono-≲ (ib₁ (ret triv)) (ib₂ (ret triv))) (λ _ → ≲-refl) ⟩
--     bind (F unit) (step (F unit) c₁ (ret triv) & step (F unit) c₂ (ret triv)) (λ _ → result)
--   ≡⟨⟩
--     step (F unit) (c₁ ⊗ c₂) result
--   ∎
