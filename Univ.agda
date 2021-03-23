{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Data.Nat.Base
open import Data.Nat.Properties
open import Eq
open import Unit 
open import Void

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
  {-# REWRITE cumul⁺ #-}
  cumul⁻ : ∀ {l k} → (h : l ≥ k) → (u : cmp (univ neg k)) → el⁻ l (lift⁻ h u) ≡ el⁻ k u
  {-# REWRITE cumul⁻ #-}
  
postulate
  Π̂ : ∀ {k} → (Â : val (univ pos k)) → (val (el⁺ k Â) → cmp (univ neg k)) → 
    cmp (univ neg k)
  Π̂/decode : ∀ {k} → (Â : val (univ pos k)) → (B̂ : val (el⁺ k Â) → cmp (univ neg k)) → 
    el⁻ k (Π̂ Â B̂) ≡ Π (el⁺ k Â) (λ a → el⁻ k (B̂ a))
  {-# REWRITE Π̂/decode #-}

postulate 
  Σ++/code : ∀ {k} → (Â : val (univ pos k)) → (val (el⁺ k Â) → val (univ pos k)) → 
    val (univ pos k)
  Σ++/code/decode : ∀ {k} → (Â : val (univ pos k)) → (B̂ : val (el⁺ k Â) → val (univ pos k)) →  
    el⁺ k (Σ++/code Â B̂) ≡ Σ++ (el⁺ _ Â) (λ a → el⁺ _ (B̂ a))
  {-# REWRITE Σ++/code/decode #-}

postulate 
  Σ+-/code : ∀ {k} → (Â : val (univ pos k)) → (val (el⁺ k Â) → cmp (univ neg k)) → 
    cmp (univ neg k)
  Σ+-/code/decode : ∀ {k} → (Â : val (univ pos k)) → (B̂ : val (el⁺ k Â) → cmp (univ neg k)) →  
    el⁻ k (Σ+-/code Â B̂) ≡ Σ+- (el⁺ _ Â) (λ a → el⁻ _ (B̂ a))
  {-# REWRITE Σ+-/code/decode #-}

postulate
  F̂ : ∀ {k} → val (univ pos k) → cmp (univ neg k)
  F̂/decode : ∀ {k} → (Â : val (univ pos k)) → el⁻ k (F̂ Â) ≡ F (el⁺ k Â)
  {-# REWRITE F̂/decode #-}

postulate
  Û : ∀ {k} → cmp (univ neg k) → val (univ pos k) 
  Û/decode : ∀ {k} → (B̂ : cmp (univ neg k)) → el⁺ k (Û B̂) ≡ U (el⁻ k B̂)
  {-# REWRITE Û/decode #-}

postulate
  eq/code : ∀ {k} → (Â : val (univ pos k)) → val (el⁺ k Â) → val (el⁺ k Â) → val (univ pos k) 
  eq/decode : ∀ {k} → (Â : val (univ pos k)) → (a1 : val (el⁺ k Â)) → (a2 : val (el⁺ k Â)) → 
    el⁺ k (eq/code Â a1 a2) ≡ eq (el⁺ k Â) a1 a2
  {-# REWRITE eq/decode #-}

postulate
  bind/decode : ∀ {k A} → (e : cmp (F A)) → (f : val A → cmp (univ neg k)) → 
    el⁻ k (bind (univ neg k) e f) ≡ tbind e (λ a → el⁻ k (f a))
  {-# REWRITE bind/decode #-}

postulate
  unit/code : val (univ pos 0)
  unit/decode : el⁺ _ unit/code ≡ unit
  {-# REWRITE unit/decode #-}

postulate
  void/code : val (univ pos 0)
  void/decode : el⁺ _ void/code ≡ void
  {-# REWRITE void/decode #-}

postulate
  ext/val/code : ∀ {k} → (ext → val (univ pos k)) → val (univ pos k)
  ext/val/code/decode : ∀ {k} →  (Â : ext → val (univ pos k)) → el⁺ k (ext/val/code Â) ≡ ext/val (λ u → el⁺ k (Â u)) 
  {-# REWRITE ext/val/code/decode #-}

postulate
  ext/cmp/code : ∀ {k} → (ext → cmp (univ neg k)) → cmp (univ neg k)
  ext/cmp/code/decode : ∀ {k} →  (Â : ext → cmp (univ neg k)) → el⁻ k (ext/cmp/code Â) ≡ ext/cmp (λ u → el⁻ k (Â u)) 
  {-# REWRITE ext/cmp/code/decode #-}

◯⁺/code : ∀ {k} → val (univ pos k) → val (univ pos k)
◯⁺/code Â = ext/val/code (λ _ → Â)

◯⁻/code : ∀ {k} → cmp (univ neg k) → cmp (univ neg k)
◯⁻/code Â = ext/cmp/code (λ _ → Â)