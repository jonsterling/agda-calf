{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.Monad

open import CalfMonad.Sequence.Array as Array using (module Sig)

open Sig

module CalfMonad.Sequence.ArraySequence2 {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid parCostMonad nondetMonad} (array : ARRAY ℓ {ℓ′} {M} monad nondetMonad {ℓ″} {ℂ} {costMonoid} {costMonad} {parCostMonoid} parCostMonad) where

open Monad monad
open ParCostMonad parCostMonad
open ARRAY array

open import Data.Bool.Base                             using (Bool; T; _∨_; false; true)
open import Data.Bool.Properties                       using (T-∨)
open import Data.Empty                                 using (⊥-elim)
open import Data.Fin.Base                              using (Fin; fromℕ<″; opposite; suc; toℕ; zero)
open import Data.Fin.Properties                        using (toℕ-fromℕ; toℕ-fromℕ<″; toℕ-inject₁; toℕ<n)
open import Data.Nat.Base                              using (_<_; _∸_; _≤_; _≡ᵇ_; _≤ᵇ_; _≤‴_; pred; suc; zero; ℕ; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties                        using (<⇒≤; <⇒≱; m>n⇒m∸n≢0; m≤n⇒m<n∨m≡n; n∸n≡0; pred[m∸n]≡m∸[1+n]; suc[pred[n]]≡n; ≤-reflexive; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤ᵇ⇒≤; ≤‴⇒≤; ≤⇒≤ᵇ; ≤‴⇒≤″)
open import Data.Sum.Base                              using ([_,_]; _⊎_; inj₁; inj₂; swap)
open import Data.Sum.Function.Propositional            using (_⊎-⇔_)
open import Data.Vec.Base                       as Vec using ()
open import Data.Vec.Relation.Unary.All                using (_∷_)
open import Data.Vec.Relation.Unary.All.Properties     using (tabulate⁺; tabulate⁻)
open import Function.Base                              using (_∘_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Equivalence                       using (Equivalence; _⇔_; equivalence; sym) renaming (_∘_ to _⇔-∘_)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; cong₂; refl; subst)

open import CalfMonad.CBPV monad
open import CalfMonad.Util as Util using (Prod)

module Spec = Array.Spec ℓ monad nondetMonad

open Util.ParCostMonad parCostMonad

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

  toℕ-opposite : ∀ {n} i → toℕ (opposite {n} i) ≡ n ∸ suc (toℕ i)
  toℕ-opposite zero = toℕ-fromℕ _
  toℕ-opposite (suc i) rewrite toℕ-inject₁ (opposite i) = toℕ-opposite i

  tabulate⁻∘tabulate⁺ : ∀ {a A p P n f} Pf i → tabulate⁻ (tabulate⁺ {a} {A} {p} {P} {n} {f} Pf) i ≡ Pf i
  tabulate⁻∘tabulate⁺ Pf zero = refl
  tabulate⁻∘tabulate⁺ Pf (suc i) = tabulate⁻∘tabulate⁺ _ i

  tabulate⁺-cong : ∀ {a A p P n f Pf Pf′} → (∀ i → Pf i ≡ Pf′ i) → tabulate⁺ {a} {A} {p} {P} {n} {f} Pf ≡ tabulate⁺ {a} {A} {p} {P} {n} {f} Pf′
  tabulate⁺-cong {n = zero} eq = refl
  tabulate⁺-cong {n = suc n} eq = cong₂ _∷_ (eq zero) (tabulate⁺-cong (eq ∘ suc))

Seq : (A : tp+) (n : ℕ) → tp+
Seq = Array

module Seq {A n} where
  nth : (as : Seq A n) (i : Fin n) → M A
  nth = Array.nth

  tabulate : (f : (i : Fin n) → M A) → M (Seq A n)
  tabulate f = Array.build (ArrayBuilder.cast cmp-≤‴-refl (b ≤‴-refl))
    module tabulate where
      cmp : ∀ {i} → i ≤‴ n → Fin n → Bool
      cmp {zero} le j = false
      cmp {suc i} le j = (toℕ (opposite (fromℕ<″ i (≤‴⇒≤″ le))) ≡ᵇ toℕ j) ∨ cmp (≤‴-step le) j

      cmp-≡ : ∀ {i} le j → cmp {i} le j ≡ (n ∸ i ≤ᵇ toℕ j)
      cmp-≡ {zero} le j = T-inj (sym ≤ᵇ⇔≤ ⇔-∘ equivalence ⊥-elim (<⇒≱ (toℕ<n j)))
      cmp-≡ {suc i} le j rewrite cmp-≡ (≤‴-step le) j rewrite toℕ-opposite (fromℕ<″ i (≤‴⇒≤″ le)) rewrite toℕ-fromℕ<″ (≤‴⇒≤″ le) = T-inj (sym ≤ᵇ⇔≤ ⇔-∘ sym m≤n⇔m<n∨m≡n ⇔-∘ subst (λ x → T (n ∸ i ≤ᵇ toℕ j) ⇔ x ≤ toℕ j) eq ≤ᵇ⇔≤ ⊎-⇔ ≡ᵇ⇔≡ ⇔-∘ swap-⇔ ⇔-∘ T-∨)
        where
          eq : n ∸ i ≡ suc (n ∸ suc i)
          eq = begin
            n ∸ i              ≡˘⟨ suc[pred[n]]≡n (m>n⇒m∸n≢0 (≤‴⇒≤ le)) ⟩
            suc (pred (n ∸ i)) ≡⟨ cong suc (pred[m∸n]≡m∸[1+n] n i) ⟩
            suc (n ∸ suc i)    ∎

      cmp-≤‴-refl : ∀ j → cmp ≤‴-refl j ≡ true
      cmp-≤‴-refl j rewrite cmp-≡ ≤‴-refl j rewrite n∸n≡0 n = refl

      b : ∀ {i} le → ArrayBuilder′ A n (cmp {i} le)
      b {zero} le = ArrayBuilder.empty
      b {suc i} le = ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f k) (ArrayBuilder.assign k)) (b (≤‴-step le))
        where
          k : Fin n
          k = opposite (fromℕ<″ i (≤‴⇒≤″ le))

  tabulate/ext : ∀ u f → tabulate f ≡ par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Vec.tabulate ∘ Prod.lookup
  tabulate/ext u f = begin
    Array.build (ArrayBuilder.cast cmp-≤‴-refl (b ≤‴-refl))                                                                  ≡⟨ Array.build/ext u _ ⟩
    ArrayBuilder.ext/toSpec u (ArrayBuilder.cast cmp-≤‴-refl (b ≤‴-refl)) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build ≡⟨ cong (_>>= pure ∘ _) b/ext ⟩
    (par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build            ≡⟨ >>=->>= _ _ _ ⟩
    par (Prod.tabulate f) >>= (λ as → pure (tabulate⁺ (Prod.lookup as)) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build)  ≡⟨ >>=-cong _ (λ as → pure->>= _ _) ⟩
    par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Spec.Array.build ∘ tabulate⁺ ∘ Prod.lookup                       ≡⟨ >>=-cong _ (λ as → cong (pure ∘ Array.ext/fromSpec u) (tabulate-cong (tabulate⁻∘tabulate⁺ _))) ⟩
    par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Vec.tabulate ∘ Prod.lookup                                       ∎
    where
      open tabulate f

      open import Data.Bool.Base using (if_then_else_)
      open import Data.Bool.Properties using (_≟_; T-≡; T-not-≡; ¬-not)
      open import Data.Fin.Base using (raise; _-_; fromℕ<; cast)
      open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective; toℕ-raise; toℕ-cast)
      open import Data.Vec.Base using (_∷_)
      open import Data.Vec.Properties using (tabulate-cong)
      open import Data.Vec.Relation.Unary.All using (All; _∷_)
      open import Data.Nat.Base using (s≤s; _+_)
      open import Data.Nat.Properties using (m∸n+n≡m; m∸[m∸n]≡n; ≡-irrelevant; +-identityʳ; +-suc; ∸-cancelʳ-≤; m<n⇒0<n∸m; n≮n)
      open import Relation.Binary.PropositionalEquality.Core as Eq using (cong₂; trans)
      open import Relation.Binary.PropositionalEquality.Properties using (subst-subst; trans-symˡ)
      open import Data.Product using (_,_)

      cast-refl : ∀ {n} i → cast {n} refl i ≡ i
      cast-refl zero = refl
      cast-refl (suc i) = cong suc (cast-refl i)

      cast≡subst : ∀ {m n} eq i → cast {m} {n} eq i ≡ subst Fin eq i
      cast≡subst refl = cast-refl

      toℕ‿- : ∀ {m} (i : Fin m) j → toℕ (i - j) ≡ toℕ i ∸ toℕ j
      toℕ‿- i zero = refl
      toℕ‿- (suc i) (suc j) = toℕ‿- i j

      Bool-≡-irrelevant : {x y : Bool} (p q : x ≡ y) → p ≡ q
      Bool-≡-irrelevant = Bool/≡-irrelevant
        where
          open import Axiom.UniquenessOfIdentityProofs
          open Decidable⇒UIP _≟_ renaming (≡-irrelevant to Bool/≡-irrelevant)

      g′ : ∀ {i} → i ≤‴ n → (Fin i → A) → ∀ (j : Fin n) {b} → (n ∸ i ≤ᵇ toℕ j) ≡ b → if b then A else _
      g′ le as j {false} eq = _
      g′ {i} le as j {true} eq = as (cast eq′ (j - fromℕ< lt))
        module g′ where
          lt : n ∸ i < suc (toℕ j)
          lt = s≤s (≤ᵇ⇒≤ _ _ (Equivalence.from T-≡ ⟨$⟩ eq))

          eq′ : n ∸ toℕ (fromℕ< lt) ≡ i
          eq′ = begin
            n ∸ toℕ (fromℕ< lt) ≡⟨ cong (n ∸_) (toℕ-fromℕ< lt) ⟩
            n ∸ (n ∸ i)         ≡⟨ m∸[m∸n]≡n (≤‴⇒≤ le) ⟩
            i                   ∎

      g : ∀ {i} le → (Fin i → A) → ∀ j → if cmp {i} le j then A else _
      g le as j = g′ le as j (Eq.sym (cmp-≡ le j))

      g-subst : ∀ {i} le as j {b} eq → g′ {i} le as j {b} eq ≡ subst (if_then A else _) eq (g′ le as j refl)
      g-subst le as j refl = refl

      g-≤‴-refl : ∀ as j → g ≤‴-refl as j ≡ subst (if_then A else _) (Eq.sym (cmp-≤‴-refl j)) (as j)
      g-≤‴-refl = {!!}
      {-
      g-≤‴-refl as j = begin
        g ≤‴-refl as j                                                                                                                                                  ≡⟨ g-subst ≤‴-refl as j _ ⟩
        subst (if_then A else _) (Eq.sym (cmp-≡ ≤‴-refl j)) (g′ ≤‴-refl as j refl)                                                                                      ≡⟨ cong (λ eq → subst (if_then A else _) eq (g′ ≤‴-refl as j refl)) (Bool-≡-irrelevant (Eq.sym (cmp-≡ ≤‴-refl j)) (Eq.trans (subst (λ b → (b ≤ᵇ toℕ j) ≡ true) (Eq.sym (n∸n≡0 n)) refl) (Eq.sym (cmp-≤‴-refl j)))) ⟩
        subst (if_then A else _) (Eq.trans (subst (λ b → (b ≤ᵇ toℕ j) ≡ true) (Eq.sym (n∸n≡0 n)) refl) (Eq.sym (cmp-≤‴-refl j))) (g′ ≤‴-refl as j refl)                 ≡˘⟨ subst-subst (subst (λ b → (b ≤ᵇ toℕ j) ≡ true) (Eq.sym (n∸n≡0 n)) refl) ⟩
        subst (if_then A else _) (Eq.sym (cmp-≤‴-refl j)) (subst (if_then A else _) (subst (λ b → (b ≤ᵇ toℕ j) ≡ true) (Eq.sym (n∸n≡0 n)) refl) (g′ ≤‴-refl as j refl)) ≡˘⟨ cong (subst (if_then A else _) (Eq.sym (cmp-≤‴-refl j))) (g-subst ≤‴-refl as j _) ⟩
        subst (if_then A else _) (Eq.sym (cmp-≤‴-refl j)) (g′ ≤‴-refl as j (subst (λ b → (b ≤ᵇ toℕ j) ≡ true) (Eq.sym (n∸n≡0 n)) refl))                                 ≡⟨ cong (subst (if_then A else _) (Eq.sym (cmp-≤‴-refl j)) ∘ as) (toℕ-injective eq) ⟩
        subst (if_then A else _) (Eq.sym (cmp-≤‴-refl j)) (as j)                                                                                                        ∎
        where
          open g′ ≤‴-refl as j (subst (λ b → (b ≤ᵇ toℕ j) ≡ true) (Eq.sym (n∸n≡0 n)) refl)

          eq : toℕ (cast eq′ (j - fromℕ< lt)) ≡ toℕ j
          eq = begin
            toℕ (cast eq′ (j - fromℕ< lt)) ≡⟨ toℕ-cast eq′ (j - fromℕ< lt) ⟩
            toℕ (j - fromℕ< lt)            ≡⟨ toℕ‿- j (fromℕ< lt) ⟩
            toℕ j ∸ toℕ (fromℕ< lt)        ≡⟨ cong (toℕ j ∸_) (toℕ-fromℕ< lt) ⟩
            toℕ j ∸ (n ∸ n)                ≡⟨ cong (toℕ j ∸_) (n∸n≡0 n) ⟩
            toℕ j                          ∎
    -}

      pf : ∀ {i} le → ArrayBuilder.ext/toSpec u (b {i} le) ≡ par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ le)) ∘ raise _)) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup
      pf {zero} le = begin
        ArrayBuilder.ext/toSpec u ArrayBuilder.empty     ≡⟨ ArrayBuilder.ext/toSpec-empty u ⟩
        pure Spec.ArrayBuilder.empty                     ≡˘⟨ pure->>= _ _ ⟩
        pure _ >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup ∎
      pf {suc i} le = begin
        ArrayBuilder.ext/toSpec u (ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f k) (ArrayBuilder.assign k)) (b (≤‴-step le))) ≡⟨ ArrayBuilder.ext/toSpec-par′ u _ _ ⟩
        (ArrayBuilder.ext/toSpec u (bind (ArrayBuilder A n _) (f k) (ArrayBuilder.assign k)) & ArrayBuilder.ext/toSpec u (b (≤‴-step le))) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ cong (λ b₁ → (b₁ & ArrayBuilder.ext/toSpec u (b (≤‴-step le))) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) (ArrayBuilder.ext/toSpec-bind u _ _) ⟩
        ((f k >>= ArrayBuilder.ext/toSpec u ∘ ArrayBuilder.assign k) & ArrayBuilder.ext/toSpec u (b (≤‴-step le))) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ cong₂ (λ b₁ b₂ → (b₁ & b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) (>>=-cong _ (ArrayBuilder.ext/toSpec-assign u k)) (pf (≤‴-step le)) ⟩
        ((f k >>= pure ∘ Spec.ArrayBuilder.assign k) & (par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) ∘ raise _)) >>= pure ∘ tabulate⁺ ∘ g (≤‴-step le) ∘ Prod.lookup)) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ cong (_>>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) (>>=-pure-&->>=-pure _ _ _ _) ⟩
        ((f k & par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) ∘ raise _))) >>= λ (a , as) → pure (Spec.ArrayBuilder.assign k a , tabulate⁺ (g (≤‴-step le) (Prod.lookup as)))) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ >>=->>= _ _ _ ⟩
        (f k & par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) ∘ raise _))) >>= (λ (a , as) → pure (Spec.ArrayBuilder.assign k a , tabulate⁺ (g (≤‴-step le) (Prod.lookup as))) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ >>=-cong _ (λ aas → pure->>= _ _) ⟩
        (f k & par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) ∘ raise _))) >>= (λ (a , as) → Spec.ArrayBuilder.par′ (Spec.ArrayBuilder.assign k a) (tabulate⁺ (g (≤‴-step le) (Prod.lookup as)))) ≡⟨ >>=-cong _ (λ aas → Spec.ArrayBuilder.par′≡seq′ _ _ disjoint) ⟩
        (f k & par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) ∘ raise _))) >>= (λ (a , as) → pure (Spec.ArrayBuilder.seq′ (Spec.ArrayBuilder.assign k a) (tabulate⁺ (g (≤‴-step le) (Prod.lookup as))))) ≡⟨ >>=-cong _ (λ aas → cong pure {!!}) ⟩
        (f k & par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) ∘ raise _))) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup ≡⟨ cong₂ (λ k es → (f k & par es) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup) (toℕ-injective foo) (Prod.tabulate-cong (cong f ∘ toℕ-injective ∘ bar)) ⟩
        (f (subst Fin (m∸n+n≡m (≤‴⇒≤ le)) (raise (n ∸ suc i) zero)) & par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ le)) ∘ raise _ ∘ suc))) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup ∎
        where
          k : Fin n
          k = opposite (fromℕ<″ i (≤‴⇒≤″ le))

          toℕ-subst : ∀ {m n} (eq : m ≡ n) i → toℕ (subst Fin eq i) ≡ toℕ i
          toℕ-subst refl i = refl

          toℕ-k : toℕ k ≡ n ∸ suc i
          toℕ-k = begin
            toℕ k                                ≡⟨ toℕ-opposite _ ⟩
            n ∸ suc (toℕ (fromℕ<″ i (≤‴⇒≤″ le))) ≡⟨ cong (λ i → n ∸ suc i) (toℕ-fromℕ<″ (≤‴⇒≤″ le)) ⟩
            n ∸ suc i                            ∎

          foo : toℕ k ≡ toℕ (subst Fin (m∸n+n≡m (≤‴⇒≤ le)) (raise (n ∸ suc i) zero))
          foo = begin
            toℕ k                                                        ≡⟨ toℕ-k ⟩
            n ∸ suc i                                                    ≡˘⟨ +-identityʳ _ ⟩
            n ∸ suc i + zero                                             ≡˘⟨ toℕ-raise _ zero ⟩
            toℕ (raise (n ∸ suc i) zero)                                 ≡˘⟨ toℕ-subst _ _ ⟩
            toℕ (subst Fin (m∸n+n≡m (≤‴⇒≤ le)) (raise (n ∸ suc i) zero)) ∎

          bar : ∀ j → toℕ (subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) (raise (n ∸ i) j)) ≡ toℕ (subst Fin (m∸n+n≡m (≤‴⇒≤ le)) (raise (n ∸ suc i) (suc j)))
          bar j = begin
            toℕ (subst Fin (m∸n+n≡m (≤‴⇒≤ (≤‴-step le))) (raise (n ∸ i) j)) ≡⟨ toℕ-subst _ _ ⟩
            toℕ (raise (n ∸ i) j)                                           ≡⟨ toℕ-raise _ j ⟩
            n ∸ i + toℕ j                                                   ≡˘⟨ cong (_+ toℕ j) (suc[pred[n]]≡n (m>n⇒m∸n≢0 (≤‴⇒≤ le))) ⟩
            suc (pred (n ∸ i)) + toℕ j                                      ≡˘⟨ +-suc _ (toℕ j) ⟩
            pred (n ∸ i) + suc (toℕ j)                                      ≡⟨ cong (_+ suc (toℕ j)) (pred[m∸n]≡m∸[1+n] n i) ⟩
            n ∸ suc i + suc (toℕ j)                                         ≡˘⟨ toℕ-raise _ (suc j) ⟩
            toℕ (raise (n ∸ suc i) (suc j))                                 ≡˘⟨ toℕ-subst _ _ ⟩
            toℕ (subst Fin (m∸n+n≡m (≤‴⇒≤ le)) (raise (n ∸ suc i) (suc j))) ∎

          disjoint : ∀ j → (toℕ k ≡ᵇ toℕ j) ≡ false ⊎ cmp (≤‴-step le) j ≡ false
          disjoint j with toℕ k ≡ᵇ toℕ j in eq
          ...           | false = inj₁ refl
          ...           | true rewrite cmp-≡ (≤‴-step le) j = inj₂ disjoint′
            where
              toℕ-j : toℕ j ≡ n ∸ suc i
              toℕ-j = begin
                toℕ j     ≡˘⟨ ≡ᵇ⇒≡ _ _ (Equivalence.from T-≡ ⟨$⟩ eq) ⟩
                toℕ k     ≡⟨ toℕ-k ⟩
                n ∸ suc i ∎

              disjoint′ : (n ∸ i ≤ᵇ toℕ j) ≡ false
              disjoint′ rewrite toℕ-j rewrite Eq.sym (pred[m∸n]≡m∸[1+n] n i) = ¬-not (n≮n zero ∘ ∸-cancelʳ-≤ (m<n⇒0<n∸m (≤‴⇒≤ le)) ∘ ≤ᵇ⇒≤ _ _ ∘ Equivalence.from T-≡ ._⟨$⟩_)

      b/ext : ArrayBuilder.ext/toSpec u (ArrayBuilder.cast cmp-≤‴-refl (b ≤‴-refl)) ≡ par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup
      b/ext = {!!}
      {-
      b/ext = begin
        ArrayBuilder.ext/toSpec u (ArrayBuilder.cast cmp-≤‴-refl (b ≤‴-refl))                                                                                          ≡⟨ ArrayBuilder.ext/toSpec-cast u cmp-≤‴-refl _ ⟩
        Spec.ArrayBuilder.cast′ cmp-≤‴-refl $⁻ ArrayBuilder.ext/toSpec u (b ≤‴-refl)                                                                                   ≡⟨ cong (Spec.ArrayBuilder.cast′ cmp-≤‴-refl $⁻_) (pf ≤‴-refl) ⟩
        Spec.ArrayBuilder.cast′ cmp-≤‴-refl $⁻ (par (Prod.tabulate (f ∘ subst Fin (m∸n+n≡m (≤‴⇒≤ ≤‴-refl)) ∘ raise _)) >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup) ≡⟨ cong (λ es → Spec.ArrayBuilder.cast′ cmp-≤‴-refl $⁻ (par es >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup)) (Prod.tabulate-cong (cong f ∘ eq)) ⟩
        Spec.ArrayBuilder.cast′ cmp-≤‴-refl $⁻ (par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup)                                                  ≡⟨ Spec.ArrayBuilder.cast′ cmp-≤‴-refl .$⁻-bind _ _ ⟩
        par (Prod.tabulate f) >>= Spec.ArrayBuilder.cast′ cmp-≤‴-refl $⁻_ ∘ pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup                                                 ≡⟨ >>=-cong _ (λ as → Spec.ArrayBuilder.cast′-pure _ _) ⟩
        par (Prod.tabulate f) >>= pure ∘ Spec.ArrayBuilder.cast cmp-≤‴-refl ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup                                                      ≡⟨ >>=-cong _ (λ as → cong pure (foo _)) ⟩
        par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup                                                                                                       ∎
        where
          raise-zero : ∀ {m} i eq → raise m i ≡ subst Fin (cong (_+ n) (Eq.sym eq)) i
          raise-zero i refl = refl

          eq : ∀ i → subst Fin (m∸n+n≡m (≤‴⇒≤ ≤‴-refl)) (raise (n ∸ n) i) ≡ i
          eq i = begin
            subst Fin (m∸n+n≡m (≤‴⇒≤ ≤‴-refl)) (raise (n ∸ n) i)                              ≡⟨ cong (subst Fin _) (raise-zero i (n∸n≡0 n)) ⟩
            subst Fin (m∸n+n≡m (≤‴⇒≤ ≤‴-refl)) (subst Fin (cong (_+ n) (Eq.sym (n∸n≡0 n))) i) ≡⟨ subst-subst (cong (_+ n) (Eq.sym (n∸n≡0 n))) ⟩
            subst Fin (trans (cong (_+ n) (Eq.sym (n∸n≡0 n))) (m∸n+n≡m (≤‴⇒≤ ≤‴-refl))) i     ≡⟨ cong (λ eq → subst Fin eq i) (≡-irrelevant _ refl) ⟩
            i                                                                                 ∎

          baz : ∀ {a A p P n f f′} eq xs → subst (All P) (tabulate-cong eq) (tabulate⁺ {a} {A} {p} {P} {n} {f} xs) ≡ tabulate⁺ {a} {A} {p} {P} {n} {f′} λ i → subst P (eq i) (xs i)
          baz {n = zero} eq xs = refl
          baz {P = P} {n = suc n} eq xs = begin
            subst (All P) (cong₂ _∷_ (eq zero) (tabulate-cong (eq ∘ suc))) (xs zero ∷ tabulate⁺ (xs ∘ suc)) ≡⟨ subst-∷ (eq zero) (tabulate-cong (eq ∘ suc)) (xs zero) (tabulate⁺ (xs ∘ suc)) ⟩
            subst P (eq zero) (xs zero) ∷ subst (All P) (tabulate-cong (eq ∘ suc)) (tabulate⁺ (xs ∘ suc))   ≡⟨ cong (subst P (eq zero) (xs zero) ∷_) (baz (eq ∘ suc) (xs ∘ suc)) ⟩
            subst P (eq zero) (xs zero) ∷ tabulate⁺ (λ i → subst P (eq (suc i)) (xs (suc i)))               ∎
            where
              subst-∷ : ∀ {a A p P n a₁ b₁ a₂ b₂} (eq₁ : a₁ ≡ b₁) (eq₂ : a₂ ≡ b₂) x₁ x₂ → subst (All {p} {a} {A} P) (cong₂ _∷_ eq₁ eq₂) (x₁ ∷ x₂) ≡ subst P eq₁ x₁ ∷ subst (All P {n}) eq₂ x₂
              subst-∷ refl refl x₁ x₂ = refl

          foo : (as : Fin n → A) → Spec.ArrayBuilder.cast cmp-≤‴-refl (tabulate⁺ (g ≤‴-refl as)) ≡ tabulate⁺ as
          foo as = trans (baz cmp-≤‴-refl (g ≤‴-refl as)) (tabulate⁺-cong eq′)
            where
              eq′ : ∀ i → subst (if_then A else _) (cmp-≤‴-refl i) (g ≤‴-refl as i) ≡ as i
              eq′ i = begin
                subst (if_then A else _) (cmp-≤‴-refl i) (g ≤‴-refl as i)                                           ≡⟨ cong (subst _ _) (g-≤‴-refl as i) ⟩
                subst (if_then A else _) (cmp-≤‴-refl i) (subst (if_then A else _) (Eq.sym (cmp-≤‴-refl i)) (as i)) ≡⟨ subst-subst (Eq.sym (cmp-≤‴-refl i)) ⟩
                subst (if_then A else _) (Eq.trans (Eq.sym (cmp-≤‴-refl i)) (cmp-≤‴-refl i)) (as i)                 ≡⟨ cong (λ eq → subst (if_then A else _) eq _) (trans-symˡ (cmp-≤‴-refl i)) ⟩
                as i                                                                                                ∎
                -}
