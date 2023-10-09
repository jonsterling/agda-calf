{-# OPTIONS --rewriting #-}

module Examples.Amortized.Simple where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Level using (0ℓ)

open import Calf costMonoid
open import Calf.Data.Product
open import Calf.Data.Bool
open import Calf.Data.Nat as Nat using (ℕ; zero; suc; nat; _+_; _∸_; pred; _*_; _^_; _>_)
open import Calf.Data.Equality as Eq using (_≡_; refl; _≡⁺_; ≡⁺-syntax; _≡⁻_; ≡⁻-syntax; module ≡-Reasoning)

open import Examples.Amortized.Core


postulate
  simple : tp⁻
record Simple : Set where
  coinductive
  field
    quit : cmp (F unit)
    next : cmp simple
postulate
  simple/decode : val (U simple) ≡ Simple
  {-# REWRITE simple/decode #-}

  quit/step : ∀ {c e} → Simple.quit (step simple c e) ≡ step (F unit) c (Simple.quit e)
  next/step : ∀ {c e} → Simple.next (step simple c e) ≡ step simple   c (Simple.next e)
  {-# REWRITE quit/step next/step #-}

{-# TERMINATING #-}
every : cmp simple
Simple.quit every = ret triv
Simple.next every = step simple 1 every

Φ : val bool → ℂ
Φ false = 1
Φ true  = 0

{-# TERMINATING #-}
alternating : cmp (Π bool λ _ → simple)
Simple.quit (alternating b) = step (F unit) (Φ b) (ret triv)
Simple.next (alternating false) = step simple 2 (alternating true)
Simple.next (alternating true ) = alternating false

record _≈_ (s₁ s₂ : cmp simple) : Set where
  coinductive
  field
    quit : Simple.quit s₁ ≡ Simple.quit s₂
    next : Simple.next s₁ ≈ Simple.next s₂
postulate
  _≈⁻_ : (s₁ s₂ : cmp simple) → tp⁻
  ≈⁻/decode : {s₁ s₂ : cmp simple} → val (U (s₁ ≈⁻ s₂)) ≡ s₁ ≈ s₂
  {-# REWRITE ≈⁻/decode #-}

≈-cong : (c : ℂ) {x y : Simple} → x ≈ y → step simple c x ≈ step simple c y
_≈_.quit (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.quit h)
_≈_.next (≈-cong c h) = ≈-cong c (_≈_.next h)

{-# TERMINATING #-}
every≈alternating : ∀ b → alternating b ≈ step simple (Φ b) every
_≈_.quit (every≈alternating _) = refl
_≈_.next (every≈alternating false) = ≈-cong 2 (every≈alternating true)
_≈_.next (every≈alternating true ) = every≈alternating false

simple-program : tp⁺
simple-program = nat

{-# TERMINATING #-}
ψ : cmp (Π simple-program λ _ → Π (U simple) λ _ → F unit)
ψ zero    s = Simple.quit s
ψ (suc n) s = ψ n (Simple.next s)

_≈'_ : (q₁ q₂ : cmp simple) → tp⁻
s₁ ≈' s₂ = Π simple-program λ p → ψ p s₁ ≡⁻[ F unit ] ψ p s₂

{-# TERMINATING #-}
classic-amortization : {s₁ s₂ : cmp simple} → val (U (s₁ ≈⁻ s₂) ⇔ U (s₁ ≈' s₂))
classic-amortization = forward , backward
  where
    forward : {s₁ s₂ : cmp simple} → s₁ ≈ s₂ → cmp (s₁ ≈' s₂)
    forward h zero    = _≈_.quit h
    forward h (suc n) = forward (_≈_.next h) n

    backward : {s₁ s₂ : cmp simple} → cmp (s₁ ≈' s₂) → s₁ ≈ s₂
    _≈_.quit (backward classic) = classic zero
    _≈_.next (backward classic) = backward (λ n → classic (suc n))
