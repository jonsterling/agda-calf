{-# OPTIONS --prop --without-K --rewriting #-}

-- Common cost monoids.

module Calf.CostMonoids where

open import Calf.CostMonoid
open import Data.Product
open import Function
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

ℕ-CostMonoid : CostMonoid
ℕ-CostMonoid = record
  { ℂ = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

ℤ-CostMonoid : CostMonoid
ℤ-CostMonoid = record
  { ℂ = ℤ
  ; _+_ = _+_
  ; zero = 0ℤ
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Integer
    open import Data.Integer.Properties

ℚ-CostMonoid : CostMonoid
ℚ-CostMonoid = record
  { ℂ = ℚ
  ; _+_ = _+_
  ; zero = 0ℚ
  ; _≤_ = _≤_
  ; isCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone = record { ∙-mono-≤ = +-mono-≤ }
    }
  }
  where
    open import Data.Rational
    open import Data.Rational.Properties

ResourceMonoid : CostMonoid
ResourceMonoid = record
  { ℂ = ℕ × ℕ
  ; _+_ = _·_
  ; zero = 0 , 0
  ; _≤_ = _≤ᵣ_
  ; isCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _·_
          }
        ; assoc = assoc
        }
      ; identity = identityˡ , identityʳ
      }
    ; isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → (≤-refl , ≤-refl) }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans h₁ h₁' , ≤-trans h₂' h₂
      }
    ; isMonotone = record { ∙-mono-≤ = {! ∙-mono-≤ᵣ !} }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Data.Sum

    open ≤-Reasoning

    open import Algebra.Definitions {A = ℕ × ℕ} _≡_
    open import Relation.Nullary
    open import Relation.Binary

    _-_ : (m n : ℕ) → n ≤ m → ℕ
    (m - n) h = m ∸ n

    _·_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
    (p , p') · (q , q') with ≤-total p' q
    ... | inj₁ p'≤q = p + (q - p') p'≤q , q'
    ... | inj₂ q≤p' = p , (q' + (p' - q) q≤p')

    _≤ᵣ_ : ℕ × ℕ → ℕ × ℕ → Set
    (p , p') ≤ᵣ (q , q') = (p ≤ q) × (q' ≤ p')


    lemma : {x y z : ℕ} → y ≡ z → x + (y ∸ z) ≡ x
    lemma {x} {y} {z} y≡z =
      begin-equality
        x + (y ∸ z)
      ≡⟨ Eq.cong (λ y → x + (y ∸ z)) y≡z ⟩
        x + (z ∸ z)
      ≡⟨ Eq.cong (x +_) (n∸n≡0 z) ⟩
        x + zero
      ≡⟨ +-identityʳ x ⟩
        x
      ∎

    arithmetic : ∀ m n o → o ≤ n → m ∸ (n ∸ o) ≡ (m + o) ∸ n
    arithmetic m       n       .zero   z≤n       = {!   !}
    arithmetic zero    (suc n) (suc o) (s≤s o≤n) = {!   !}
    arithmetic (suc m) (suc n) (suc o) (s≤s o≤n) = {!   !}

    ∸-cancelˡ-≤ : ∀ {m n o} → o ≤ m → o ≤ n → m ∸ o ≤ n ∸ o → m ≤ n
    ∸-cancelˡ-≤ = {!   !}

    assoc : Associative _·_
    assoc (p , p') (q , q') (r , r') with ≤-total p' q | ≤-total q' r
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r with ≤-total q' r | ≤-total p' (q + (r - q') q'≤r)
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₁ _ | inj₁ _ =
      Eq.cong
        (_, r')
        (begin-equality
          p + (q ∸ p') + (r ∸ q')
        ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
          p + ((q ∸ p') + (r ∸ q'))
        ≡˘⟨ Eq.cong (p +_) (+-∸-comm (r ∸ q') p'≤q) ⟩
          p + (q + (r ∸ q') ∸ p')
        ∎)
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₁ _ | inj₂ q+r∸q'≤p' =
      let q+r∸q'≡p' = ≤-antisym q+r∸q'≤p' (≤-trans p'≤q (m≤m+n q (r ∸ q'))) in
      Eq.cong₂
        _,_
        (begin-equality
          p + (q ∸ p') + (r ∸ q')
        ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
          p + ((q ∸ p') + (r ∸ q'))
        ≡˘⟨ Eq.cong (p +_) (+-∸-comm (r ∸ q') p'≤q) ⟩
          p + ((q + (r ∸ q')) ∸ p')
        ≡⟨ Eq.cong (λ x → p + (x ∸ p')) q+r∸q'≡p' ⟩
          p + (p' ∸ p')
        ≡⟨ Eq.cong (p +_) (n∸n≡0 p') ⟩
          p + zero
        ≡⟨ +-identityʳ p ⟩
          p
        ∎)
        (begin-equality
          r'
        ≡˘⟨ +-identityʳ r' ⟩
          r' + zero
        ≡˘⟨ Eq.cong (r' +_) (n∸n≡0 p') ⟩
          r' + (p' ∸ p')
        ≡˘⟨ Eq.cong (λ x → r' + (p' ∸ x)) q+r∸q'≡p' ⟩
          r' + (p' ∸ (q + (r ∸ q')))
        ∎)
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₂ r≤q' | inj₁ _ =
      let q'≡r = ≤-antisym q'≤r r≤q' in
      Eq.cong₂
        (λ x y → p + x , y)
        (Eq.cong (_∸ p') (Eq.sym (lemma (Eq.sym q'≡r))))
        (lemma q'≡r)
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₂ r≤q' | inj₂ q+r∸q'≤p' =
      let q'≡r = ≤-antisym q'≤r r≤q' in
      let p'≡q = ≤-antisym p'≤q (m+n≤o⇒m≤o q q+r∸q'≤p') in
      Eq.cong₂
        (λ x y → x , r' + y)
        (lemma (Eq.sym p'≡q))
        (begin-equality
          q' ∸ r
        ≡⟨ Eq.cong (_∸ r) q'≡r ⟩
          r ∸ r
        ≡⟨ n∸n≡0 r ⟩
          zero
        ≡˘⟨ n∸n≡0 q ⟩
          q ∸ q
        ≡˘⟨ Eq.cong (_∸ q) p'≡q ⟩
          p' ∸ q
        ≡˘⟨ Eq.cong (p' ∸_) {y = q} (lemma (Eq.sym q'≡r)) ⟩
          p' ∸ (q + (r ∸ q'))
        ∎)
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' with ≤-total q' r | ≤-total p' q
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' | inj₁ q'≤r | inj₁ _ =
      let q'≡r = ≤-antisym q'≤r r≤q' in
      Eq.cong₂
        _,_
        (begin-equality
          p + (q ∸ p') + (r ∸ q')
        ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
          p + ((q ∸ p') + (r ∸ q'))
        ≡⟨ Eq.cong (p +_) (lemma (Eq.sym q'≡r)) ⟩
          p + (q ∸ p')
        ∎)
        (Eq.sym (lemma q'≡r))
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' | inj₁ q'≤r | inj₂ q≤p' =
      let p'≡q = ≤-antisym p'≤q q≤p' in
      let q'≡r = ≤-antisym q'≤r r≤q' in
      Eq.cong₂
        _,_
        (begin-equality
          p + (q ∸ p') + (r ∸ q')
        ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
          p + ((q ∸ p') + (r ∸ q'))
        ≡⟨ Eq.cong (p +_) (lemma (Eq.sym q'≡r)) ⟩
          p + (q ∸ p')
        ≡⟨ lemma (Eq.sym p'≡q) ⟩
          p
        ∎)
        (begin-equality
          r'
        ≡˘⟨ lemma q'≡r ⟩
          r' + (q' ∸ r)
        ≡˘⟨ Eq.cong (r' +_) (lemma p'≡q) ⟩
          r' + ((q' ∸ r) + (p' ∸ q))
        ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
          r' + (q' ∸ r) + (p' ∸ q)
        ∎)
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' | inj₂ _ | inj₁ _ = refl
    assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' | inj₂ _ | inj₂ q≤p' =
      let p'≡q = ≤-antisym p'≤q q≤p' in
      Eq.cong₂
        _,_
        (lemma (Eq.sym p'≡q))
        (begin-equality
          r' + (q' ∸ r)
        ≡˘⟨ Eq.cong (r' +_) (lemma p'≡q) ⟩
          r' + ((q' ∸ r) + (p' ∸ q))
        ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
          (r' + (q' ∸ r)) + (p' ∸ q)
        ∎)
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r with ≤-total (q' + (p' ∸ q)) r | ≤-total p' (q + (r ∸ q'))
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₁ _ | inj₁ p'≤q+[r∸q'] =
      Eq.cong
        (λ x → p + x , r')
        (begin-equality
          r ∸ (q' + (p' ∸ q))
        ≡˘⟨ ∸-+-assoc r q' (p' ∸ q) ⟩
          (r ∸ q') ∸ (p' ∸ q)
        ≡⟨ arithmetic (r ∸ q') p' q q≤p' ⟩
          ((r ∸ q') + q) ∸ p'
        ≡⟨ Eq.cong (_∸ p') (+-comm (r ∸ q') q) ⟩
          (q + (r ∸ q')) ∸ p'
        ∎)
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₁ q'+[p'∸q]≤r | inj₂ q+[r∸q']≤p' =
      let
        r≤q'+[p'∸q] : r ≤ q' + (p' ∸ q)
        r≤q'+[p'∸q] =
          ∸-cancelˡ-≤ {o = q'} q'≤r (m≤m+n q' (p' ∸ q)) $
          +-cancelˡ-≤ q (r ∸ q') ((q' + (p' ∸ q)) ∸ q') $
          begin
            q + (r ∸ q')
          ≤⟨ q+[r∸q']≤p' ⟩
            p'
          ≡˘⟨ +-identityʳ p' ⟩
            p' + zero
          ≡˘⟨ Eq.cong (p' +_) (n∸n≡0 q) ⟩
            p' + (q ∸ q)
          ≡˘⟨ +-∸-assoc p' {q} ≤-refl ⟩
            (p' + q) ∸ q
          ≡⟨ Eq.cong (_∸ q) (+-comm p' q) ⟩
            (q + p') ∸ q
          ≡⟨ +-∸-assoc q q≤p' ⟩
            q + (p' ∸ q)
          ≡˘⟨ Eq.cong (λ x → q + (x + (p' ∸ q))) (n∸n≡0 q') ⟩
            q + ((q' ∸ q') + (p' ∸ q))
          ≡˘⟨ Eq.cong (q +_) (+-∸-comm {q'} (p' ∸ q) ≤-refl) ⟩
            q + ((q' + (p' ∸ q)) ∸ q')
          ∎
      in
      let
        p'≤q+[r∸q'] : p' ≤ q + (r ∸ q')
        p'≤q+[r∸q'] =
          ∸-cancelˡ-≤ q≤p' (m≤m+n q (r ∸ q')) $
          +-cancelˡ-≤ q' (p' ∸ q) ((q + (r ∸ q')) ∸ q) $
          {!   !}
      in
      Eq.cong₂
        _,_
        (lemma (≤-antisym r≤q'+[p'∸q] q'+[p'∸q]≤r))
        (Eq.sym (lemma (≤-antisym p'≤q+[r∸q'] q+[r∸q']≤p')))
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₂ _ | inj₁ _ = {!   !}
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₂ r≤q'+[p'∸q] | inj₂ _ =
      Eq.cong
        (λ x → p , r' + x)
        (begin-equality
          (q' + (p' ∸ q)) ∸ r
        ≡⟨ +-∸-assoc q' {p' ∸ q} {r} {!   !} ⟩
          q' + ((p' ∸ q) ∸ r)
        ≡⟨ Eq.cong (q' +_) (∸-+-assoc p' q r) ⟩
          q' + (p' ∸ (q + r))
        ≡⟨ {!   !} ⟩
          p' ∸ (q + (r ∸ q'))
        ∎)
        -- (begin-equality
        --   r' + ((q' + (p' ∸ q)) ∸ r)
        -- ≡˘⟨ +-∸-assoc r' {q' + (p' ∸ q)} {r} r≤q'+[p'∸q] ⟩
        --   (r' + (q' + (p' ∸ q))) ∸ r
        -- ≡⟨ {!   !} ⟩
        --   r' + (p' ∸ (q + (r ∸ q')))
        -- ∎)
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' with ≤-total (q' + (p' ∸ q)) r | ≤-total p' q
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' | inj₁ _ | inj₁ _ = {!   !}
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' | inj₁ _ | inj₂ _ = {!   !}
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' | inj₂ _ | inj₁ _ = {!   !}
    assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' | inj₂ _ | inj₂ _ = {!   !}

    -- assoc : Associative _·_
    -- assoc (p , p') (q , q') (r , r') with ≤-total p' q
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q with ≤-total q' r
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r with ≤-total p' (q + (r ∸ q'))
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₁ _ =
    --   let open ≡-Reasoning in
    --   Eq.cong
    --     (_, r')
    --     (begin
    --       p + (q ∸ p') + (r ∸ q')
    --     ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
    --       p + ((q ∸ p') + (r ∸ q'))
    --     ≡˘⟨ Eq.cong (p +_) (+-∸-comm (r ∸ q') p'≤q) ⟩
    --       p + (q + (r ∸ q') ∸ p')
    --     ∎)
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₂ h =
    --   let open ≡-Reasoning in
    --   let q+r∸q'≡p' = ≤-antisym (≤-trans p'≤q (m≤m+n q (r ∸ q'))) h in
    --   Eq.cong₂
    --     _,_
    --     (begin
    --       p + (q ∸ p') + (r ∸ q')
    --     ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
    --       p + ((q ∸ p') + (r ∸ q'))
    --     ≡˘⟨ Eq.cong (p +_) (+-∸-comm (r ∸ q') p'≤q) ⟩
    --       p + ((q + (r ∸ q')) ∸ p')
    --     ≡˘⟨ Eq.cong (λ x → p + (x ∸ p')) q+r∸q'≡p' ⟩
    --       p + (p' ∸ p')
    --     ≡⟨ Eq.cong (p +_) (n∸n≡0 p') ⟩
    --       p + zero
    --     ≡⟨ +-identityʳ p ⟩
    --       p
    --     ∎)
    --     (begin
    --       r'
    --     ≡˘⟨ +-identityʳ r' ⟩
    --       r' + zero
    --     ≡˘⟨ Eq.cong (r' +_) (n∸n≡0 p') ⟩
    --       r' + (p' ∸ p')
    --     ≡⟨ Eq.cong (λ x → r' + (p' ∸ x)) q+r∸q'≡p' ⟩
    --       r' + (p' ∸ (q + (r ∸ q')))
    --     ∎)
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' with ≤-total p' q
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' | inj₁ _ = refl
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' | inj₂ q≤p' =
    --   let open ≡-Reasoning in
    --   let p'≡q = ≤-antisym p'≤q q≤p' in
    --   Eq.cong₂
    --     _,_
    --     (begin
    --       p + (q ∸ p')
    --     ≡⟨ Eq.cong (λ x → p + (q ∸ x)) p'≡q ⟩
    --       p + (q ∸ q)
    --     ≡⟨ Eq.cong (p +_) (n∸n≡0 q) ⟩
    --       p + zero
    --     ≡⟨ +-identityʳ p ⟩
    --       p
    --     ∎)
    --     (begin
    --       r' + (q' ∸ r)
    --     ≡˘⟨ +-identityʳ (r' + (q' ∸ r)) ⟩
    --       (r' + (q' ∸ r)) + zero
    --     ≡˘⟨ Eq.cong ((r' + (q' ∸ r)) +_) (n∸n≡0 q) ⟩
    --       (r' + (q' ∸ r)) + (q ∸ q)
    --     ≡˘⟨ Eq.cong (λ x → (r' + (q' ∸ r)) + (x ∸ q)) p'≡q ⟩
    --       (r' + (q' ∸ r)) + (p' ∸ q)
    --     ∎)
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' with ≤-total q' r
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r = {!   !}
    -- -- with ≤-total (q' + (p' ∸ q)) r
    -- -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₁ x = {!   !}
    -- -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₂ y = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' = {!   !}

    -- | ≤-total (q' + (p' ∸ q)) r
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₁ x = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r | inj₂ y = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' | inj₁ x = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' | inj₂ y = {!   !}

    -- assoc (p , p') (q , q') (r , r') with ≤-total p' q | ≤-total q' r
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r with ≤-total q' r | ≤-total p' (q + (r ∸ q'))
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₁ _ | inj₁ h =
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₁ _ | inj₂ h = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₂ _ | inj₁ h = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₁ q'≤r | inj₂ _ | inj₂ h = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₁ p'≤q | inj₂ r≤q' = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₁ q'≤r = {!   !}
    -- assoc (p , p') (q , q') (r , r') | inj₂ q≤p' | inj₂ r≤q' = {!   !}

    -- with p' ≤? q | q' ≤? r
    -- assoc (p , p') (q , q') (r , r') | yes p'≤q | yes q'≤r with q' ≤? r | p' ≤? q + (r ∸ q')
    -- assoc (p , p') (q , q') (r , r') | yes p'≤q | yes q'≤r | yes _ | yes h =
    --   let open ≡-Reasoning in
    --   Eq.cong
    --     (_, r')
    --     (begin
    --       p + (q ∸ p') + (r ∸ q')
    --     ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
    --       p + ((q ∸ p') + (r ∸ q'))
    --     ≡˘⟨ Eq.cong (p +_) (+-∸-comm {q} (r ∸ q') {p'} p'≤q) ⟩
    --       p + (q + (r ∸ q') ∸ p')
    --     ∎)
    -- assoc (p , p') (q , q') (r , r') | yes p'≤q | yes q'≤r | yes q'≤r-other | no ¬h =
    --   let open ≡-Reasoning in
    --   Eq.cong₂
    --     _,_
    --     (begin
    --       p + (q ∸ p') + (r ∸ q')
    --     ≡⟨ +-assoc p (q ∸ p') (r ∸ q') ⟩
    --       p + ((q ∸ p') + (r ∸ q'))
    --     ≡⟨ {!   !} ⟩
    --       p
    --     ∎)
    --     (begin
    --       {!   !}
    --     ≡⟨ {!   !} ⟩
    --       {!   !}
    --     ∎)
    -- assoc (p , p') (q , q') (r , r') | yes p'≤q | yes q'≤r | no ¬q'≤r | _ = contradiction q'≤r ¬q'≤r
    --   -- let open ≡-Reasoning in
    --   -- begin
    --   --   {!   !}
    --   -- ≡⟨ {!   !} ⟩
    --   --   {!   !}
    --   -- ∎
    -- assoc (p , p') (q , q') (r , r') | yes p'≤q | no ¬q'≤r = {!   !}
    -- assoc (p , p') (q , q') (r , r') | no ¬p'≤q | yes q'≤r = {!   !}
    -- assoc (p , p') (q , q') (r , r') | no ¬p'≤q | no ¬q'≤r = {!   !}
    -- -- with p' ≤ᵇ q
    -- -- assoc (p , p') (q , q') (r , r') | true with q' ≤ᵇ r
    -- -- assoc (p , p') (q , q') (r , r') | true | true with p' ≤ᵇ q + (r ∸ q')
    -- -- assoc (p , p') (q , q') (r , r') | true | true | true = {!   !}
    -- -- assoc (p , p') (q , q') (r , r') | true | true | false = {!   !}
    -- -- assoc (p , p') (q , q') (r , r') | true | false = {!   !}
    -- -- with p' ≤? q
    -- -- ... | yes _ = {!   !}
    -- -- ... | yes p'≤q | yes q'≤r = {! (p + (q ∸ p') , q') · (r , r')  !}
    -- -- ... | yes p'≤q | no ¬q'≤r = {!   !}
    -- -- assoc (p , p') (q , q') (r , r') | no ¬p'≤q = {!   !}

    -- -- m≤n⇒m≤n+o : ∀ {m n o} → m ≤ n → m ≤ n + o
    -- -- m≤n⇒m≤n+o {m} {n} {o} h =
    -- --   begin
    -- --     m
    -- --   ≡˘⟨ +-identityʳ m ⟩
    -- --     m + 0
    -- --   ≤⟨ +-mono-≤ h z≤n ⟩
    -- --     n + o
    -- --   ∎
    -- --     where open ≤-Reasoning

    -- -- assoc : Associative _·_
    -- -- assoc (p , p') (q , q') (r , r') with q' ≤? r
    -- -- assoc (p , p') (q , q') (r , r') | no ¬h₁ with p' ≤? q
    -- -- assoc (p , p') (q , q') (r , r') | no ¬h₁ | no ¬h₂ with q' + (p' ∸ q) ≤? r
    -- -- assoc (p , p') (q , q') (r , r') | no ¬h₁ | no ¬h₂ | no ¬h₃ =
    -- --   let h₁ = ≰⇒≥ ¬h₁ in
    -- --   Eq.cong (p ,_)
    -- --     (begin
    -- --       r' + (q' + (p' ∸ q) ∸ r)
    -- --     ≡⟨ Eq.cong (r' +_) (+-∸-comm (p' ∸ q) h₁) ⟩
    -- --       r' + ((q' ∸ r) + (p' ∸ q))
    -- --     ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
    -- --       r' + (q' ∸ r) + (p' ∸ q)
    -- --     ∎)
    -- --       where open ≡-Reasoning
    -- -- assoc (p , p') (q , q') (r , r') | no ¬h₁ | no ¬h₂ | yes h₃ =
    -- --   let h₁ = ≰⇒≥ ¬h₁ in
    -- --   Eq.cong₂ _,_
    -- --     (begin
    -- --       p + (r ∸ (q' + (p' ∸ q)))
    -- --     ≡⟨ Eq.cong (p +_) (Eq.subst (λ n → (r ∸ n) ≡ 0) (≤-antisym (m≤n⇒m≤n+o h₁) h₃) (n∸n≡0 r)) ⟩
    -- --       p + 0
    -- --     ≡⟨ +-identityʳ p ⟩
    -- --       p
    -- --     ∎)
    -- --     (begin
    -- --       r'
    -- --     ≡˘⟨ +-identityʳ r' ⟩
    -- --       r' + 0
    -- --     ≡˘⟨ Eq.cong (r' +_) (Eq.subst (λ n → (n ∸ r) ≡ 0) (≤-antisym (m≤n⇒m≤n+o h₁) h₃) (n∸n≡0 r)) ⟩
    -- --       r' + (q' + (p' ∸ q) ∸ r)
    -- --     ≡⟨ Eq.cong (r' +_) (+-∸-comm (p' ∸ q) h₁) ⟩
    -- --       r' + ((q' ∸ r) + (p' ∸ q))
    -- --     ≡˘⟨ +-assoc r' (q' ∸ r) (p' ∸ q) ⟩
    -- --       r' + (q' ∸ r) + (p' ∸ q)
    -- --     ∎)
    -- --       where open ≡-Reasoning
    -- -- assoc (p , p') (q , q') (r , r') | no ¬h₁ | yes h₂ = {!   !}
    -- -- assoc (p , p') (q , q') (r , r') | yes h₁ = {!   !}

    identityˡ : LeftIdentity (0 , 0) _·_
    identityˡ (q , q') = Eq.cong₂ _,_ (+-identityˡ q) (+-identityˡ q')

    identityʳ : RightIdentity (0 , 0) _·_
    identityʳ (q , q') with ≤-total q' 0
    ... | inj₁ z≤n = Eq.cong (_, 0) (+-identityʳ q)
    ... | inj₂ _   = refl

    -- ∙-mono-≤ᵣ : _·_ Preserves₂ _≤ᵣ_ ⟶ _≤ᵣ_ ⟶ _≤ᵣ_
    -- ∙-mono-≤ᵣ {p , p'} {q , q'} {r , r'} {s , s'} (h₁ , h₂) (h₁' , h₂') with p' ≤? r | q' ≤? s
    -- ... | no ¬p₁ | no ¬p₂ = h₁ , +-mono-≤ h₂' (∸-mono h₂ h₁')
    -- ... | no ¬p₁ | yes p₂ =
    --   let p₁ = ≰⇒≥ ¬p₁ in
    --   (
    --     begin
    --       p
    --     ≤⟨ h₁ ⟩
    --       q
    --     ≡˘⟨ +-identityʳ q ⟩
    --       q + 0
    --     ≡˘⟨ Eq.cong (q +_) (m≤n⇒m∸n≡0 p₁) ⟩
    --       q + (r ∸ p')
    --     ≤⟨ +-monoʳ-≤ q (∸-mono h₁' h₂) ⟩
    --       q + (s ∸ q')
    --     ∎
    --   ) , (
    --     begin
    --       s'
    --     ≤⟨ h₂' ⟩
    --       r'
    --     ≡˘⟨ +-identityʳ r' ⟩
    --       r' + 0
    --     ≡˘⟨ Eq.cong (r' +_) (m≤n⇒m∸n≡0 p₂) ⟩
    --       r' + (q' ∸ s)
    --     ≤⟨ +-monoʳ-≤ r' (∸-mono h₂ h₁') ⟩
    --       r' + (p' ∸ r)
    --     ∎
    --   )
    --     where open ≤-Reasoning
    -- ... | yes p₁ | no ¬p₂ =
    --   let p₂ = ≰⇒≥ ¬p₂ in
    --   (
    --     begin
    --       p + (r ∸ p')
    --     ≤⟨ +-monoʳ-≤ p (∸-mono h₁' h₂) ⟩
    --       p + (s ∸ q')
    --     ≡⟨ Eq.cong (p +_) (m≤n⇒m∸n≡0 p₂) ⟩
    --       p + 0
    --     ≡⟨ +-identityʳ p ⟩
    --       p
    --     ≤⟨ h₁ ⟩
    --       q
    --     ∎
    --   ) , (
    --     begin
    --       s' + (q' ∸ s)
    --     ≤⟨ +-monoʳ-≤ s' (∸-mono h₂ h₁') ⟩
    --       s' + (p' ∸ r)
    --     ≡⟨ Eq.cong (s' +_) (m≤n⇒m∸n≡0 p₁) ⟩
    --       s' + 0
    --     ≡⟨ +-identityʳ s' ⟩
    --       s'
    --     ≤⟨ h₂' ⟩
    --       r'
    --     ∎
    --   )
    --     where open ≤-Reasoning
    -- ... | yes p₁ | yes p₂ = +-mono-≤ h₁ (∸-mono h₁' h₂) , h₂'

sequentialParCostMonoid :
  (cm : CostMonoid)
  → IsCommutativeMonoid (CostMonoid._+_ cm) (CostMonoid.zero cm)
  → ParCostMonoid
sequentialParCostMonoid cm isCommutativeMonoid = record
  { ℂ = ℂ cm
  ; _⊕_ = _+_ cm
  ; 𝟘 = zero cm
  ; _⊗_ = _+_ cm
  ; 𝟙 = zero cm
  ; _≤_ = _≤_ cm
  ; isParCostMonoid = record
    { isMonoid = isMonoid cm
    ; isCommutativeMonoid = isCommutativeMonoid
    ; isPreorder = isPreorder cm
    ; isMonotone-⊕ = isMonotone cm
    ; isMonotone-⊗ = isMonotone cm
    }
  }
  where open CostMonoid

ℕ-Work-ParCostMonoid : ParCostMonoid
ℕ-Work-ParCostMonoid = sequentialParCostMonoid ℕ-CostMonoid +-0-isCommutativeMonoid
  where open import Data.Nat.Properties using (+-0-isCommutativeMonoid)

ℕ-Span-ParCostMonoid : ParCostMonoid
ℕ-Span-ParCostMonoid = record
  { ℂ = ℕ
  ; _⊕_ = _+_
  ; 𝟘 = 0
  ; _⊗_ = _⊔_
  ; 𝟙 = 0
  ; _≤_ = _≤_
  ; isParCostMonoid = record
    { isMonoid = +-0-isMonoid
    ; isCommutativeMonoid = ⊔-0-isCommutativeMonoid
    ; isPreorder = ≤-isPreorder
    ; isMonotone-⊕ = record { ∙-mono-≤ = +-mono-≤ }
    ; isMonotone-⊗ = record { ∙-mono-≤ = ⊔-mono-≤ }
    }
  }
  where
    open import Data.Nat
    open import Data.Nat.Properties

combineParCostMonoids : ParCostMonoid → ParCostMonoid → ParCostMonoid
combineParCostMonoids pcm₁ pcm₂ = record
  { ℂ = ℂ pcm₁ × ℂ pcm₂
  ; _⊕_ = λ (a₁ , a₂) (b₁ , b₂) → _⊕_ pcm₁ a₁ b₁ , _⊕_ pcm₂ a₂ b₂
  ; 𝟘 = 𝟘 pcm₁ , 𝟘 pcm₂
  ; _⊗_ = λ (a₁ , a₂) (b₁ , b₂) → _⊗_ pcm₁ a₁ b₁ , _⊗_ pcm₂ a₂ b₂
  ; 𝟙 = 𝟙 pcm₁ , 𝟙 pcm₂
  ; _≤_ = λ (a₁ , a₂) (b₁ , b₂) → _≤_ pcm₁ a₁ b₁ × _≤_ pcm₂ a₂ b₂
  ; isParCostMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = Eq.isEquivalence
          ; ∙-cong = Eq.cong₂ _
          }
        ; assoc = λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) → Eq.cong₂ _,_ (⊕-assoc pcm₁ a₁ b₁ c₁) (⊕-assoc pcm₂ a₂ b₂ c₂)
        }
      ; identity =
        (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊕-identityˡ pcm₁ a₁) (⊕-identityˡ pcm₂ a₂)) ,
        (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊕-identityʳ pcm₁ a₁) (⊕-identityʳ pcm₂ a₂))
      }
    ; isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = Eq.isEquivalence
            ; ∙-cong = Eq.cong₂ _
            }
          ; assoc = λ (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) → Eq.cong₂ _,_ (⊗-assoc pcm₁ a₁ b₁ c₁) (⊗-assoc pcm₂ a₂ b₂ c₂)
          }
        ; identity =
          (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊗-identityˡ pcm₁ a₁) (⊗-identityˡ pcm₂ a₂)) ,
          (λ (a₁ , a₂) → Eq.cong₂ _,_ (⊗-identityʳ pcm₁ a₁) (⊗-identityʳ pcm₂ a₂))
        }
      ; comm = λ (a₁ , a₂) (b₁ , b₂) → Eq.cong₂ _,_ (⊗-comm pcm₁ a₁ b₁) (⊗-comm pcm₂ a₂ b₂)
      }
    ; isPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ { refl → ≤-refl pcm₁ , ≤-refl pcm₂ }
      ; trans = λ (h₁ , h₂) (h₁' , h₂') → ≤-trans pcm₁ h₁ h₁' , ≤-trans pcm₂ h₂ h₂'
      }
    ; isMonotone-⊕ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊕-mono-≤ pcm₁ h₁ h₁' , ⊕-mono-≤ pcm₂ h₂ h₂'
      }
    ; isMonotone-⊗ = record
      { ∙-mono-≤ = λ (h₁ , h₂) (h₁' , h₂') → ⊗-mono-≤ pcm₁ h₁ h₁' , ⊗-mono-≤ pcm₂ h₂ h₂'
      }
    }
  }
  where open ParCostMonoid

ℕ²-ParCostMonoid : ParCostMonoid
ℕ²-ParCostMonoid = combineParCostMonoids ℕ-Work-ParCostMonoid ℕ-Span-ParCostMonoid
