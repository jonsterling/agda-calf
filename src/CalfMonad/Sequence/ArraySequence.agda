{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.Monad

open import CalfMonad.Sequence.Array as Array using (module Sig)

open Sig

module CalfMonad.Sequence.ArraySequence {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid parCostMonad nondetMonad} (array : ARRAY ℓ {ℓ′} {M} monad nondetMonad {ℓ″} {ℂ} {costMonoid} {costMonad} {parCostMonoid} parCostMonad) where

open Monad monad
open ARRAY array

open import Data.Bool.Base                             using (Bool; T; _∨_; false; true)
open import Data.Bool.Properties                       using (T-∨)
open import Data.Empty                                 using (⊥-elim)
open import Data.Fin.Base                              using (Fin; fromℕ<″; suc; toℕ; zero)
open import Data.Fin.Properties                        using (toℕ-fromℕ<″; toℕ<n)
open import Data.Nat.Base                              using (_<_; _≤_; _≡ᵇ_; _≤ᵇ_; _≤‴_; ℕ; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties                        using (0≤‴n; <⇒≤; <⇒≱; m≤n⇒m<n∨m≡n; ≤-reflexive; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤‴⇒≤″)
open import Data.Sum.Base                              using ([_,_]; _⊎_; swap)
open import Data.Sum.Function.Propositional            using (_⊎-⇔_)
open import Data.Vec.Base                   as Vec     using ()
open import Data.Vec.Properties                        using (tabulate-cong)
open import Data.Vec.Relation.Unary.All.Properties     using (tabulate⁺; tabulate⁻)
open import Function.Base                              using (_∘_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Equivalence                       using (Equivalence; _⇔_; equivalence; sym) renaming (_∘_ to _⇔-∘_)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; refl)

open import CalfMonad.CBPV monad
open import CalfMonad.Util

module Spec = Array.Spec ℓ monad nondetMonad

open ParCostMonad parCostMonad

open ≡-Reasoning

private
  T-inj : ∀ {x y} → T x ⇔ T y → x ≡ y
  T-inj {true}  {true}  eqv = refl
  T-inj {false} {false} eqv = refl
  T-inj {true}  {false} eqv = ⊥-elim (Equivalence.to   eqv ⟨$⟩ _)
  T-inj {false} {true}  eqv = ⊥-elim (Equivalence.from eqv ⟨$⟩ _)

  module _ {m n} where
    ≡ᵇ⇔≡ : T (m ≡ᵇ n) ⇔ m ≡ n
    ≡ᵇ⇔≡ = equivalence (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n)

    ≤ᵇ⇔≤ : T (m ≤ᵇ n) ⇔ m ≤ n
    ≤ᵇ⇔≤ = equivalence (≤ᵇ⇒≤ m n) ≤⇒≤ᵇ

    m≤n⇔m<n∨m≡n : m ≤ n ⇔ (m < n ⊎ m ≡ n)
    m≤n⇔m<n∨m≡n = equivalence m≤n⇒m<n∨m≡n [ <⇒≤ , ≤-reflexive ]

  swap-⇔ : ∀ {a} {A : Set a} {b} {B : Set b} → (A ⊎ B) ⇔ (B ⊎ A)
  swap-⇔ = equivalence swap swap

  tabulate⁻∘tabulate⁺ : ∀ {a A p P n f} Pf i → tabulate⁻ (tabulate⁺ {a} {A} {p} {P} {n} {f} Pf) i ≡ Pf i
  tabulate⁻∘tabulate⁺ Pf zero = refl
  tabulate⁻∘tabulate⁺ Pf (suc i) = tabulate⁻∘tabulate⁺ _ i

Seq : (A : tp+) (n : ℕ) → tp+
Seq = Array

module Seq {A n} where
  nth : (as : Seq A n) (i : Fin n) → M A
  nth = Array.nth

  tabulate : (f : (i : Fin n) → M A) → M (Seq A n)
  tabulate f = Array.build (ArrayBuilder.cast (cmp-≡ 0≤‴n) (b 0≤‴n))
    module tabulate where
      cmp : ∀ {i} → i ≤‴ n → Fin n → Bool
      cmp ≤‴-refl j = false
      cmp (≤‴-step le) j = (toℕ (fromℕ<″ _ (≤‴⇒≤″ le)) ≡ᵇ toℕ j) ∨ cmp le j

      cmp-≡ : ∀ {i} le j → cmp {i} le j ≡ (i ≤ᵇ toℕ j)
      cmp-≡ ≤‴-refl j = T-inj (sym ≤ᵇ⇔≤ ⇔-∘ equivalence ⊥-elim (<⇒≱ (toℕ<n j)))
      cmp-≡ (≤‴-step le) j rewrite cmp-≡ le j rewrite toℕ-fromℕ<″ (≤‴⇒≤″ le) = T-inj (sym ≤ᵇ⇔≤ ⇔-∘ sym m≤n⇔m<n∨m≡n ⇔-∘ ≤ᵇ⇔≤ {n = toℕ j} ⊎-⇔ ≡ᵇ⇔≡ ⇔-∘ swap-⇔ ⇔-∘ T-∨)

      b : ∀ {i} le → ArrayBuilder′ A n (cmp {i} le)
      b ≤‴-refl = ArrayBuilder.empty
      b (≤‴-step le) = ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le)
        where
          i : Fin n
          i = fromℕ<″ _ (≤‴⇒≤″ le)

  tabulate/ext : ∀ u f → tabulate f ≡ par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Vec.tabulate ∘ Prod.lookup
  tabulate/ext u f = begin
    Array.build (ArrayBuilder.cast (cmp-≡ 0≤‴n) (b 0≤‴n))                                                                   ≡⟨ Array.build/ext u _ ⟩
    ArrayBuilder.ext/toSpec u (ArrayBuilder.cast (cmp-≡ 0≤‴n) (b 0≤‴n)) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build  ≡⟨ cong (_>>= pure ∘ _) b/ext ⟩
    (par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build           ≡⟨ >>=->>= _ _ _ ⟩
    par (Prod.tabulate f) >>= (λ as → pure (tabulate⁺ (Prod.lookup as)) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build) ≡⟨ >>=-cong _ (λ as → pure->>= _ _) ⟩
    par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build ∘ tabulate⁺ ∘ Prod.lookup                      ≡⟨ >>=-cong _ (λ as → cong (pure ∘ Array.ext/fromSpec u) (tabulate-cong (tabulate⁻∘tabulate⁺ _))) ⟩
    par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Vec.tabulate ∘ Prod.lookup                                      ∎
    where
      open tabulate f

      b/ext : ArrayBuilder.ext/toSpec u (ArrayBuilder.cast (cmp-≡ 0≤‴n) (b 0≤‴n)) ≡ par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup
      b/ext = {!!}
