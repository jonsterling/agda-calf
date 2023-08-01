{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Sequence.Array

open Sig

module CalfMonad.Sequence.ArraySequence {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid parCostMonad nondetMonad} (array : ARRAY ℓ {ℓ′} {M} monad nondetMonad {ℓ″} {ℂ} {costMonoid} {costMonad} {parCostMonoid} parCostMonad) where

open ARRAY array

open import Agda.Builtin.Equality
open import Data.Bool.Base                             using (T; false; true)
open import Data.Bool.Properties                       using (T-∨)
open import Data.Empty                                 using (⊥-elim)
open import Data.Fin.Base                              using (Fin; fromℕ<″; toℕ)
open import Data.Fin.Properties                        using (toℕ-fromℕ<″; toℕ<n)
open import Data.Nat.Base                              using (_<_; _<ᵇ_; _≤_; _≡ᵇ_; _≤ᵇ_; _≤‴_; ℕ; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties                        using (0≤‴n; <⇒<ᵇ; <⇒≤; <⇒≱; <ᵇ⇒<; m≤n⇒m<n∨m≡n; ≤-reflexive; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤‴⇒≤″)
open import Data.Sum.Base                              using ([_,_]; _⊎_; swap)
open import Data.Sum.Function.Propositional            using (_⊎-⇔_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Equivalence                       using (Equivalence; _⇔_; _∘_; equivalence; sym)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

open import CalfMonad.CBPV monad

private
  T-inj : ∀ {x y} → T x ⇔ T y → x ≡ y
  T-inj {true}  {true}  eqv = refl
  T-inj {false} {false} eqv = refl
  T-inj {true}  {false} eqv = ⊥-elim (Equivalence.to   eqv ⟨$⟩ _)
  T-inj {false} {true}  eqv = ⊥-elim (Equivalence.from eqv ⟨$⟩ _)

  module _ {m n} where
    <ᵇ⇔< : T (m <ᵇ n) ⇔ m < n
    <ᵇ⇔< = equivalence (<ᵇ⇒< m n) <⇒<ᵇ

    ≡ᵇ⇔≡ : T (m ≡ᵇ n) ⇔ m ≡ n
    ≡ᵇ⇔≡ = equivalence (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n)

    ≤ᵇ⇔≤ : T (m ≤ᵇ n) ⇔ m ≤ n
    ≤ᵇ⇔≤ = equivalence (≤ᵇ⇒≤ m n) ≤⇒≤ᵇ

    m≤n⇔m<n∨m≡n : m ≤ n ⇔ (m < n ⊎ m ≡ n)
    m≤n⇔m<n∨m≡n = equivalence m≤n⇒m<n∨m≡n [ <⇒≤ , ≤-reflexive ]

  swap-⇔ : ∀ {a} {A : Set a} {b} {B : Set b} → (A ⊎ B) ⇔ (B ⊎ A)
  swap-⇔ = equivalence swap swap

Seq : (A : tp+) (n : ℕ) → tp+
Seq = Array

module Seq {A n} where
  nth : (as : Seq A n) (i : Fin n) → M A
  nth = Array.nth

  tabulate : (f : (i : Fin n) → M A) → M (Seq A n)
  tabulate f = Array.build (b 0≤‴n)
    where
      b : ∀ {i} → i ≤‴ n → ArrayBuilder′ A n λ j → i ≤ᵇ toℕ j
      b ≤‴-refl =
        ArrayBuilder.cast (λ i → T-inj (sym ≤ᵇ⇔≤ ∘ equivalence ⊥-elim (<⇒≱ (toℕ<n i))))
        ArrayBuilder.empty
      b (≤‴-step le) =
        ArrayBuilder.cast (λ j → T-inj (sym ≤ᵇ⇔≤ ∘ sym m≤n⇔m<n∨m≡n ∘ <ᵇ⇔< ⊎-⇔ subst (λ x → T (toℕ i ≡ᵇ _) ⇔ x ≡ _) (toℕ-fromℕ<″ (≤‴⇒≤″ le)) ≡ᵇ⇔≡ ∘ swap-⇔ ∘ T-∨))
        (ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le))
        where
          i : Fin n
          i = fromℕ<″ _ (≤‴⇒≤″ le)
