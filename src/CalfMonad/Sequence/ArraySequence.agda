{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.Monad

open import CalfMonad.Sequence.Array as Array using (module Sig)

open Sig

module CalfMonad.Sequence.ArraySequence {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid parCostMonad nondetMonad} (array : ARRAY ℓ {ℓ′} {M} monad nondetMonad {ℓ″} {ℂ} {costMonoid} {costMonad} {parCostMonoid} parCostMonad) where

open Monad monad
open ParCostMonad parCostMonad
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
open import Function.Equivalence                       using (Equivalence; _⇔_; equivalence) renaming (_∘_ to _⇔-∘_; sym to ⇔-sym)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; refl; sym)

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
      cmp-≡ ≤‴-refl j = T-inj (⇔-sym ≤ᵇ⇔≤ ⇔-∘ equivalence ⊥-elim (<⇒≱ (toℕ<n j)))
      cmp-≡ (≤‴-step le) j rewrite cmp-≡ le j rewrite toℕ-fromℕ<″ (≤‴⇒≤″ le) = T-inj (⇔-sym ≤ᵇ⇔≤ ⇔-∘ ⇔-sym m≤n⇔m<n∨m≡n ⇔-∘ ≤ᵇ⇔≤ {n = toℕ j} ⊎-⇔ ≡ᵇ⇔≡ ⇔-∘ swap-⇔ ⇔-∘ T-∨)

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

      open Data.Bool.Base using (if_then_else_)
      open Data.Bool.Properties using (T-≡)
      open Data.Nat.Base using (_∸_; s≤s; zero; suc; pred)
      open Data.Nat.Properties using (m+[n∸m]≡n; ≤‴⇒≤; n∸n≡0)
      open Data.Fin.Base using (raise; _-_; fromℕ<)
      open Data.Fin.Properties using (toℕ-fromℕ<; ¬Fin0)
      open Relation.Binary.PropositionalEquality.Core using (subst; cong₂)
      open import Data.Product using (_×_; _,_)

      g : ∀ {i} le → (Fin (n ∸ i) → A) → ∀ j → if cmp {i} le j then A else _
      g {i} le as j rewrite cmp-≡ le j with i ≤ᵇ toℕ j in eq
      ...                                 | false = _
      ...                                 | true = as (subst Fin (cong (n ∸_) (toℕ-fromℕ< lt)) (j - fromℕ< lt))
        where
          lt : i < toℕ (suc j)
          lt = s≤s (≤ᵇ⇒≤ i _ (Equivalence.from T-≡ ⟨$⟩ eq))

      par-zero : ∀ {n As} es eq → par {n} {As} es ≡ pure (Prod.tabulate (⊥-elim ∘ ¬Fin0 ∘ subst Fin eq))
      par-zero es refl = refl

      cong₂′ : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c} (f : ∀ x → B x → C) {x₁ x₂ y₁ y₂} (eq : x₁ ≡ x₂) → subst B eq y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
      cong₂′ f refl refl = refl

      Prod-cong₂′ : ∀ {n n′} eq {a} As → Prod {n} {a} (As ∘ subst Fin eq) ≡ Prod {n′} {a} As
      Prod-cong₂′ refl As = refl

      par-suc : ∀ {n As} es {m} eq → par {n} {As} es ≡ subst M (Prod-cong₂′ eq As) (Prod.lookup es (subst Fin eq zero) & par {m} (Prod.tabulate (Prod.lookup es ∘ subst Fin eq ∘ suc)))
      par-suc (e , es) refl = cong (λ es → e & par es) (sym (Prod.tabulate-lookup es))

      pf : ∀ {i} le → ArrayBuilder.ext/toSpec u (b {i} le) ≡ par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ le)) ∘ raise i)) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup
      pf ≤‴-refl = begin
        ArrayBuilder.ext/toSpec u ArrayBuilder.empty                                                                            ≡⟨ ArrayBuilder.ext/toSpec-empty u ⟩
        pure Spec.ArrayBuilder.empty                                                                                            ≡˘⟨ pure->>= _ _ ⟩
        pure (Prod.tabulate (⊥-elim ∘ ¬Fin0 ∘ subst Fin (n∸n≡0 n))) >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup              ≡˘⟨ cong (_>>= _) (par-zero _ (n∸n≡0 n)) ⟩
        par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ ≤‴-refl)) ∘ raise n)) >>= pure ∘ tabulate⁺ ∘ g ≤‴-refl ∘ Prod.lookup ∎
      pf {i′} (≤‴-step le) =
        ArrayBuilder.ext/toSpec u (ArrayBuilder.par′ (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) (b le)) ≡⟨ ArrayBuilder.ext/toSpec-par′ u _ _ ⟩
        (ArrayBuilder.ext/toSpec u (bind (ArrayBuilder A n _) (f i) (ArrayBuilder.assign i)) & ArrayBuilder.ext/toSpec u (b le)) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ cong (λ b₁ → (b₁ & ArrayBuilder.ext/toSpec u (b le)) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) (ArrayBuilder.ext/toSpec-bind u _ _) ⟩
        ((f i >>= ArrayBuilder.ext/toSpec u ∘ ArrayBuilder.assign i) & ArrayBuilder.ext/toSpec u (b le)) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ cong₂ (λ b₁ b₂ → (b₁ & b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) (>>=-cong _ (ArrayBuilder.ext/toSpec-assign u _)) (pf le) ⟩
        ((f i >>= pure ∘ Spec.ArrayBuilder.assign i) & (par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ le)) ∘ raise (suc i′))) >>= pure ∘ tabulate⁺ ∘ g le ∘ Prod.lookup)) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ cong (_>>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) (>>=-pure-&->>=-pure _ _ _ _) ⟩
        ((f i & par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ le)) ∘ raise (suc i′)))) >>= λ (a , as) → pure (Spec.ArrayBuilder.assign i a , tabulate⁺ (g le (Prod.lookup as)))) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ >>=->>= _ _ _ ⟩
        (f i & par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ le)) ∘ raise (suc i′)))) >>= (λ (a , as) → pure (Spec.ArrayBuilder.assign i a , tabulate⁺ (g le (Prod.lookup as))) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂) ≡⟨ >>=-cong _ (λ aas → pure->>= _ _) ⟩
        (f i & par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ le)) ∘ raise (suc i′)))) >>= (λ (a , as) → Spec.ArrayBuilder.par′ (Spec.ArrayBuilder.assign i a) (tabulate⁺ (g le (Prod.lookup as)))) ≡⟨ {!!} ⟩
        par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ (≤‴-step le))) ∘ raise i′)) >>= {!!} ≡⟨ {!!} ⟩
        par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ (≤‴-step le))) ∘ raise i′)) >>= pure ∘ tabulate⁺ ∘ g (≤‴-step le) ∘ Prod.lookup ∎
        where
          i : Fin n
          i = fromℕ<″ i′ (≤‴⇒≤″ le)

        -- ArrayBuilder.ext/toSpec u (ArrayBuilder.par′ b₁ b₂)
        -- ArrayBuilder.castSpec′ _ ((ArrayBuilder.ext/toSpec u b₁ & ArrayBuilder.ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)

      pf′ : ArrayBuilder.ext/toSpec u (b 0≤‴n) ≡ par (Prod.tabulate f) >>= Spec.ArrayBuilder.cast′ (sym ∘ cmp-≡ 0≤‴n) ∘ pure ∘ tabulate⁺ ∘ Prod.lookup
      pf′ = begin
        ArrayBuilder.ext/toSpec u (b 0≤‴n)                                                                                ≡⟨ pf 0≤‴n ⟩
        par (Prod.tabulate (f ∘ subst Fin (m+[n∸m]≡n (≤‴⇒≤ 0≤‴n)) ∘ raise 0)) >>= pure ∘ tabulate⁺ ∘ g 0≤‴n ∘ Prod.lookup ≡⟨ {!g 0≤‴n!} ⟩
        par (Prod.tabulate f) >>= Spec.ArrayBuilder.cast′ (sym ∘ cmp-≡ 0≤‴n) ∘ pure ∘ tabulate⁺ ∘ Prod.lookup             ∎

      b/ext : ArrayBuilder.ext/toSpec u (ArrayBuilder.cast (cmp-≡ 0≤‴n) (b 0≤‴n)) ≡ par (Prod.tabulate f) >>= pure ∘ tabulate⁺ ∘ Prod.lookup
      b/ext = {!!}
