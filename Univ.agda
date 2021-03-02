{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import Data.Nat.Base
open import Data.Nat.Properties

≥-refl : ∀ {k} → k ≥ k 
≥-refl = ≤-reflexive refl
≥-trans : ∀ {m l k} → (m ≥ l) → (l ≥ k) → (m ≥ k) 
≥-trans h1 h2 = ≤-trans h2 h1

-- from Jon's AN OK VERSION OF TYPE THEORY
postulate 
  univ : (m : mode) → ℕ → tp m
  el⁺ : (k : ℕ) → val (univ pos k) → tp pos
  el⁻ : (k : ℕ) → cmp (univ neg k) → tp neg
  Û⁺ : ∀ {l k} → k < l → val (univ pos l)
  Û⁻ : ∀ {l k} → k < l → cmp (univ neg l)
  Û⁺/decode : ∀ {l k} → (h : k < l) → el⁺ l (Û⁺ h) ≡ univ pos k
  {-# REWRITE Û⁺/decode #-}
  Û⁻/decode : ∀ {l k} → (h : k < l) → el⁻ l (Û⁻ h) ≡ univ neg k
  {-# REWRITE Û⁻/decode #-}
  lift⁺ : ∀ {l k} → l ≥ k → (u : val (univ pos k)) → val (univ pos l)
  lift⁻ : ∀ {l k} → l ≥ k → (u : cmp (univ neg k)) → cmp (univ neg l)
  lift⁺/unit : ∀ {k} → (u : val (univ pos k)) → lift⁺ {k} {k} ≥-refl u ≡ u 
  lift⁻/unit : ∀ {k} → (u : cmp (univ neg k)) → lift⁻ {k} {k} ≥-refl u ≡ u 
  lift⁺/assoc : ∀ {m l k} → (h1 : m ≥ l) → (h2 : l ≥ k) → (u : val (univ pos k)) →
    lift⁺ h1 (lift⁺ h2 u) ≡ lift⁺ (≥-trans h1 h2) u
  lift⁻/assoc : ∀ {m l k} → (h1 : m ≥ l) → (h2 : l ≥ k) → (u : cmp (univ neg k)) →
    lift⁻ h1 (lift⁻ h2 u) ≡ lift⁻ (≥-trans h1 h2) u
  cumul⁺ : ∀ {l k} → (h : l ≥ k) → (u : val (univ pos k)) → el⁺ l (lift⁺ h u) ≡ el⁺ k u
  cumul⁻ : ∀ {l k} → (h : l ≥ k) → (u : cmp (univ neg k)) → el⁻ l (lift⁻ h u) ≡ el⁻ k u
  
postulate
  Π̂ : ∀ {k} → (Â : val (univ pos k)) → (val (el⁺ k Â) → cmp (univ neg k)) → 
    cmp (univ neg k)
  Π̂/decode : ∀ {k} → (Â : val (univ pos k)) → (B̂ : val (el⁺ k Â) → cmp (univ neg k)) → 
    el⁻ k (Π̂ Â B̂) ≡ Π (el⁺ k Â) (λ a → el⁻ k (B̂ a))

postulate
  F̂ : ∀ {k} → val (univ pos k) → cmp (univ neg k)
  F̂/decode : ∀ {k} → (Â : val (univ pos k)) → el⁻ k (F̂ Â) ≡ F (el⁺ k Â)

postulate
  Û : ∀ {k} → cmp (univ neg k) → val (univ pos k) 
  Û/decode : ∀ {k} → (B̂ : cmp (univ neg k)) → el⁺ k (Û B̂) ≡ U (el⁻ k B̂)