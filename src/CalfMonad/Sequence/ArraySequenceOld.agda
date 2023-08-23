{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.Monad

open import CalfMonad.Sequence.Array

open Sig

module CalfMonad.Sequence.ArraySequence {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid parCostMonad nondetMonad} (array : ARRAY ℓ {ℓ′} {M} monad nondetMonad {ℓ″} {ℂ} {costMonoid} {costMonad} {parCostMonoid} parCostMonad) where

open Monad monad
open ParCostMonad parCostMonad
open ARRAY array

open import Agda.Builtin.Equality
open import Data.Bool.Base                             using (T; false; true)
open import Data.Bool.Properties                       using (T-∨)
open import Data.Empty                                 using (⊥-elim)
open import Data.Fin.Base                              using (Fin; fromℕ<″; suc; toℕ; zero)
open import Data.Fin.Properties                        using (toℕ-fromℕ<″; toℕ<n)
open import Data.Nat.Base                              using (_<_; _<ᵇ_; _≤_; _≡ᵇ_; _≤ᵇ_; _≤‴_; ℕ; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties                        using (0≤‴n; <⇒<ᵇ; <⇒≤; <⇒≱; <ᵇ⇒<; m≤n⇒m<n∨m≡n; ≤-reflexive; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤‴⇒≤″)
open import Data.Sum.Base                              using ([_,_]; _⊎_; swap)
open import Data.Sum.Function.Propositional            using (_⊎-⇔_)
open import Data.Vec.Base                       as Vec using ()
open import Data.Vec.Properties                        using (tabulate-cong)
open import Data.Vec.Relation.Unary.All.Properties     using (tabulate⁺; tabulate⁻)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Equivalence                       using (Equivalence; _⇔_; equivalence; sym)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; refl; subst)

open import CalfMonad.CBPV monad
open import CalfMonad.Util as Util using (Prod)

module ArraySpec = Spec ℓ monad nondetMonad

open ≡-Reasoning

open Util.ParCostMonad parCostMonad

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

  tabulate⁻∘tabulate⁺ : ∀ {a A p P n f} Pf i → tabulate⁻ (tabulate⁺ {a} {A} {p} {P} {n} {f} Pf) i ≡ Pf i
  tabulate⁻∘tabulate⁺ Pf zero = refl
  tabulate⁻∘tabulate⁺ Pf (suc i) = tabulate⁻∘tabulate⁺ _ i

Seq : (A : tp+) (n : ℕ) → tp+
Seq = Array

module Seq {A n} where
  nth : (as : Seq A n) (i : Fin n) → M A
  nth = Array.nth

  tabulate : (f : (i : Fin n) → M A) → M (Seq A n)
  tabulate f = Array.build (b 0≤‴n)
    module tabulate where
      open Function.Equivalence using (_∘_)

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

  tabulate′ : (f : (i : Fin n) → M A) → M (Seq A n)
  tabulate′ f = Array.build {!b n!}
    where
      open Data.Nat.Base using (zero; suc)
      open Data.Fin.Base using (opposite)

      b : (i : ℕ) → ArrayBuilder′ A n λ j → toℕ (opposite j) <ᵇ i
      b zero = ArrayBuilder.empty
      b (suc i) = ArrayBuilder.cast {!!} (ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f {!!}) (ArrayBuilder.assign {!!})) (b i))

{-
  open import Function.Base using (_∘_)

  tabulate/ext : ∀ u f → tabulate f ≡ par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Vec.tabulate ∘ Prod.lookup
  tabulate/ext u f = begin
    Array.build (b 0≤‴n)                                                                                                         ≡⟨ Array.build/ext u _ ⟩
    ArrayBuilder.ext/toSpec u (b 0≤‴n) >>= pure ∘ Array.ext/fromSpec u ∘ ArraySpec.Array.build                                   ≡⟨ cong (_>>= pure ∘ _) b/ext ⟩
    (par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup) >>= pure ∘ Array.ext/fromSpec u ∘ ArraySpec.Array.build           ≡⟨ >>=->>= _ _ _ ⟩
    par (Prod.tabulate f) >>= (λ as → pure (tabulate⁺ (Prod.lookup as)) >>= pure ∘ Array.ext/fromSpec u ∘ ArraySpec.Array.build) ≡⟨ >>=-cong _ (λ as → pure->>= _ _) ⟩
    par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ ArraySpec.Array.build ∘ tabulate⁺ ∘ Prod.lookup                      ≡⟨ >>=-cong _ (λ as → cong (pure ∘ Array.ext/fromSpec u) (tabulate-cong (tabulate⁻∘tabulate⁺ _))) ⟩
    par (Prod.tabulate f) >>= pure ∘ Array.ext/fromSpec u ∘ Vec.tabulate ∘ Prod.lookup                                           ∎
    where
      open tabulate f

      open Data.Nat.Base using (zero; suc; _∸_; s≤s; pred)
      open Data.Fin.Base using (raise; _-_; fromℕ<)
      open Data.Fin.Properties using (toℕ-fromℕ<)
      open Data.Nat.Properties using (m+[n∸m]≡n; ≤‴⇒≤; n∸n≡0; ≡-irrelevant; suc[pred[n]]≡n)
      open Data.Bool.Base using (if_then_else_; _∨_)
      open Data.Bool.Properties using (T-≡)
      open import Data.Product using (_×_; _,_)
      open import Data.Vec.Base using (_∷_)
      open Data.Vec.Properties using (lookup∘tabulate)
      open import Data.Vec.Relation.Unary.All using (All; _∷_)
      open Relation.Binary.PropositionalEquality.Core using (cong₂; trans; _≢_) renaming (sym to Eq-sym)
      open Function.Equivalence using () renaming (_∘_ to _⇔-∘_)

      pf : ∀ {n} j → false ≡ (n ≤ᵇ toℕ {n} j)
      pf i = T-inj (sym ≤ᵇ⇔≤ ⇔-∘ equivalence ⊥-elim (<⇒≱ (toℕ<n i)))

      pf′ : ∀ {i} (le : suc i ≤‴ n) (j : Fin n) → (toℕ (fromℕ<″ _ (≤‴⇒≤″ le)) ≡ᵇ toℕ j) ∨ (i <ᵇ toℕ j) ≡ (i ≤ᵇ toℕ j)
      pf′ le j = T-inj (sym ≤ᵇ⇔≤ ⇔-∘ sym m≤n⇔m<n∨m≡n ⇔-∘ <ᵇ⇔< ⊎-⇔ subst (λ x → T (toℕ (fromℕ<″ _ (≤‴⇒≤″ le)) ≡ᵇ _) ⇔ x ≡ _) (toℕ-fromℕ<″ (≤‴⇒≤″ le)) ≡ᵇ⇔≡ ⇔-∘ swap-⇔ ⇔-∘ T-∨)

      tabulate⁺-cong : ∀ {a A p P n f Pf Pf′} → (∀ i → Pf i ≡ Pf′ i) → tabulate⁺ {a} {A} {p} {P} {n} {f} Pf ≡ tabulate⁺ Pf′
      tabulate⁺-cong {n = zero} eq = refl
      tabulate⁺-cong {n = suc n} eq = cong₂ _∷_ (eq zero) (tabulate⁺-cong λ i → eq _)

      g-help : ∀ {i} → i ≤‴ n → (Fin (n ∸ i) → A) → ∀ j {b} → (i ≤ᵇ toℕ j) ≡ b → if b then A else _
      g-help {i} le as j {false} eq = _
      g-help {i} le as j {true}  eq = as (subst Fin (cong (n ∸_) (toℕ-fromℕ< lt)) (j - fromℕ< lt))
        where
          lt : i < suc (toℕ j)
          lt = s≤s (≤ᵇ⇒≤ i _ (Equivalence.from T-≡ ⟨$⟩ eq))

      g : ∀ {i} → i ≤‴ n → (Fin (n ∸ i) → A) → ∀ j → if i ≤ᵇ toℕ j then A else _
      g le as j = g-help le as j refl

      g-help-cong : ∀ {i} le {as as′} → (∀ j → as j ≡ as′ j) → ∀ j {b} eq → g-help {i} le as j {b} eq ≡ g-help le as′ j eq
      g-help-cong {i} le pf j {false} eq = refl
      g-help-cong {i} le pf j {true}  eq = pf _

      g-cong : ∀ {i} le {as as′} → (∀ j → as j ≡ as′ j) → ∀ j → g {i} le as j ≡ g le as′ j
      g-cong le pf j = g-help-cong le pf j refl

      par-0 : ∀ {n As es} (eq : n ≡ zero) → par {n} {As} es ≡ pure (Prod.tabulate ((λ ()) ∘ subst Fin eq))
      par-0 refl = refl

      par->0 : ∀ {n As es} (ne : n ≢ zero) → par {n} {As} es ≡ subst M {!!} (par {suc (pred n)} {subst (λ n → Fin n → tp+) (Eq-sym (suc[pred[n]]≡n ne)) As} {!!})
      par->0 = {!!}

      subst-f : ∀ {a A p P q Q x y} (eq : x ≡ y) (f : ∀ {x} → P x → Q x) Px → subst {a} {A} {q} Q eq (f Px) ≡ f (subst {a} {A} {p} P eq Px)
      subst-f refl f Px = refl

      subst-∷ : ∀ {a A p P n a₁ b₁ a₂ b₂} (eq₁ : a₁ ≡ b₁) (eq₂ : a₂ ≡ b₂) x₁ x₂ → subst (All {p} {a} {A} P) (cong₂ _∷_ eq₁ eq₂) (x₁ ∷ x₂) ≡ subst P eq₁ x₁ ∷ subst (All P {n}) eq₂ x₂
      subst-∷ refl refl x₁ x₂ = refl

      subst-flip : ∀ {a A p P x y} eq {Px Py} → Px ≡ subst P (Eq-sym eq) Py → subst {a} {A} {p} P {x} {y} eq Px ≡ Py
      subst-flip refl h = h

      subst-tabulate⁺ : ∀ {n m m′} (f : ∀ i → if m i then A else _) (eq : ∀ i → m i ≡ m′ i) → subst (ArraySpec.ArrayBuilder A n) {x = Vec.tabulate m} {y = Vec.tabulate m′} (tabulate-cong eq) (tabulate⁺ f) ≡ tabulate⁺ λ i → subst (if_then A else _) (eq i) (f i)
      subst-tabulate⁺ {zero} f eq = refl
      subst-tabulate⁺ {suc n} f eq = begin
        subst (All (if_then A else _)) (cong₂ _∷_ (eq zero) (tabulate-cong λ i → eq (suc i))) (f zero ∷ tabulate⁺ λ i → f (suc i)) ≡⟨ subst-∷ (eq zero) (tabulate-cong λ i → eq (suc i)) (f zero) (tabulate⁺ λ i → f (suc i)) ⟩
        subst (if_then A else _) (eq zero) (f zero) ∷ subst (All (if_then A else _)) (tabulate-cong λ i → eq (suc i)) (tabulate⁺ λ i → f (suc i)) ≡⟨ cong (subst (if_then A else _) (eq zero) (f zero) ∷_) (subst-tabulate⁺ (λ i → f (suc i)) λ i → eq (suc i)) ⟩
        subst (if_then A else _) (eq zero) (f zero) ∷ tabulate⁺ (λ i → subst (if_then A else _) (eq (suc i)) (f (suc i))) ∎

      foo : ∀ {i} le → ArrayBuilder.ext/toSpec u (b {i} le) ≡ par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ le)) ∘ raise i)) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup
      foo {i} ≤‴-refl = {!!}{-begin
        ArrayBuilder.ext/toSpec u (ArrayBuilder.cast pf ArrayBuilder.empty) ≡⟨ ArrayBuilder.ext/toSpec-cast u _ _ ⟩
        ArrayBuilder.castSpec′ pf (ArrayBuilder.ext/toSpec u ArrayBuilder.empty) ≡⟨ cong (ArrayBuilder.castSpec′ pf ∘ ArrayBuilder.ext/toSpec u) (ArrayBuilder.empty/ext u) ⟩
        ArrayBuilder.castSpec′ pf (ArrayBuilder.ext/toSpec u (ArrayBuilder.ext/fromSpec u (pure ArraySpec.ArrayBuilder.empty))) ≡⟨ cong (ArrayBuilder.castSpec′ pf) (ArrayBuilder.ext/toSpec-fromSpec u _) ⟩
        ArrayBuilder.castSpec′ pf (pure ArraySpec.ArrayBuilder.empty) ≡⟨ subst-f _ pure _ ⟩
        pure (ArrayBuilder.castSpec pf ArraySpec.ArrayBuilder.empty) ≡⟨ cong pure (subst-tabulate⁺ _ pf) ⟩
        pure (tabulate⁺ λ j → subst (if_then A else _) {x = false} {y = i ≤ᵇ toℕ j} (pf j) _) ≡⟨ cong pure (tabulate⁺-cong λ j → subst-flip (pf j) refl) ⟩
        pure (tabulate⁺ (g ≤‴-refl (Prod.lookup (Prod.tabulate ((λ ()) ∘ subst Fin (n∸n≡0 n)))))) ≡˘⟨ pure->>= _ _ ⟩
        pure (Prod.tabulate ((λ ()) ∘ subst Fin (n∸n≡0 n))) >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup ≡˘⟨ cong (_>>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ _) (par-0 (n∸n≡0 n)) ⟩
        par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ ≤‴-refl)) ∘ raise n)) >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup ∎
        -}
      foo {i′} (≤‴-step le) = begin
        ArrayBuilder.ext/toSpec u (ArrayBuilder.cast (pf′ le) (ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le))) ≡⟨ ArrayBuilder.ext/toSpec-cast u _ _ ⟩
        ArrayBuilder.castSpec′ (pf′ le) (ArrayBuilder.ext/toSpec u (ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le))) ≡⟨ cong (ArrayBuilder.castSpec′ (pf′ le)) (ArrayBuilder.ext/toSpec-cast u _ _) ⟩
        ArrayBuilder.castSpec′ (pf′ le) (ArrayBuilder.castSpec′ (λ j → cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (ArrayBuilder.ext/toSpec u (ArrayBuilder.par (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le)))) ≡⟨ ArrayBuilder.castSpec′∘castSpec′ _ _ _ ⟩
        ArrayBuilder.castSpec′ (λ j → trans (cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (pf′ le j)) (ArrayBuilder.ext/toSpec u (ArrayBuilder.par (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le))) ≡⟨ cong (ArrayBuilder.castSpec′ (λ j → trans (cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (pf′ le j)) ∘ ArrayBuilder.ext/toSpec u) (ArrayBuilder.par/ext u _ _) ⟩
        ArrayBuilder.castSpec′ (λ j → trans (cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (pf′ le j)) (ArrayBuilder.ext/toSpec u (ArrayBuilder.ext/fromSpec u ((ArrayBuilder.ext/toSpec u (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) & ArrayBuilder.ext/toSpec u (b le)) >>= λ (b₁ , b₂) → ArraySpec.ArrayBuilder.par b₁ b₂))) ≡⟨ cong (ArrayBuilder.castSpec′ (λ j → trans (cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (pf′ le j))) (ArrayBuilder.ext/toSpec-fromSpec u _) ⟩
        ArrayBuilder.castSpec′ (λ j → trans (cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (pf′ le j)) ((ArrayBuilder.ext/toSpec u (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) & ArrayBuilder.ext/toSpec u (b le)) >>= λ (b₁ , b₂) → ArraySpec.ArrayBuilder.par b₁ b₂) ≡⟨ {!!} ⟩
        ArrayBuilder.castSpec′ (λ j → trans (cong₂ _∨_ (lookup∘tabulate _ j) (lookup∘tabulate _ j)) (pf′ le j)) (((f i >>= ArrayBuilder.ext/toSpec u ∘ ArrayBuilder.assign i) & ArrayBuilder.ext/toSpec u (b le)) >>= λ (b₁ , b₂) → ArraySpec.ArrayBuilder.par b₁ b₂) ≡⟨ {!!} ⟩
        par {n = n ∸ i′} (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ (≤‴-step le))) ∘ raise i′)) >>= pure ∘ tabulate⁺ ∘ g (≤‴-step le) ∘ Prod.lookup ∎
        where
          i : Fin n
          i = fromℕ<″ _ (≤‴⇒≤″ le)

      b/ext : ArrayBuilder.ext/toSpec u (b 0≤‴n) ≡ par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup
      b/ext = subst (λ f → ArrayBuilder.ext/toSpec u (b 0≤‴n) ≡ par f >>= pure ∘ tabulate⁺ ∘ Prod.lookup) (Prod.tabulate-cong λ i → cong f (lemma _ i)) (foo 0≤‴n)
        where
          lemma : ∀ {n} (eq : n ≡ n) i → subst Fin eq i ≡ i
          lemma eq i rewrite ≡-irrelevant eq refl = refl
-}
