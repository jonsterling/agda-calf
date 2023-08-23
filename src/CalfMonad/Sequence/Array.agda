{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.Array ℓ where

open Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Bool.Base                                  using (Bool; _∨_; false; if_then_else_; true)
open import Data.Fin.Base                                   using (Fin; toℕ)
open import Data.Product                                    using (_×_; _,_)
open import Data.Sum.Base                                   using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base                      using (⊤)
open import Data.Vec.Base                                   using (Vec; lookup; tabulate)
open import Data.Vec.Properties                             using (lookup∘tabulate; tabulate-cong)
open import Data.Vec.Relation.Unary.All             as All  using (All)
open import Data.Vec.Relation.Unary.All.Properties          using (tabulate⁺; tabulate⁻)
open import Function.Equality                               using (_⟨$⟩_)
open import Function.Inverse                                using (Inverse; _↔_; id)
open import Level                                           using (lift)
open import Relation.Binary.PropositionalEquality.Core      using (module ≡-Reasoning; _≡_; cong; cong₂; refl; subst; subst₂; sym)

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoids
open import CalfMonad.Monad
open import CalfMonad.NondetMonad
open import CalfMonad.Util using (Prod; tabulate⁺-cong)

open ≡-Reasoning

data ArrayStep : Set (lsuc ℓ) where
  read  : {A : Set ℓ} {n : Nat} (as : Vec A n) (i : Fin n) → ArrayStep
  write : {A : Set ℓ} {n : Nat} (i : Fin n) (a : A)        → ArrayStep
  alloc : (A : Set ℓ) (n : Nat)                            → ArrayStep

ℕ-ArrayStep : ArrayStep → Nat
ℕ-ArrayStep (read  as i) = 1
ℕ-ArrayStep (write i  a) = 1
ℕ-ArrayStep (alloc A  n) = 0

ℕ²-ArrayStep : ArrayStep → Nat × Nat
ℕ²-ArrayStep = ×-Step ℕ-ArrayStep ℕ-ArrayStep

module _ {ℓ′ M} (monad : Monad {ℓ} {ℓ′} M) (nondetMonad : NondetMonad M) where
  open Monad monad
  open NondetMonad nondetMonad

  module Util = CalfMonad.Util.Monad monad

  open import CalfMonad.CBPV monad

  module Spec where
    ArrayBuilder : ∀ (A : tp+) n (m : Vec Bool n) → tp+
    ArrayBuilder A n = All (if_then A else ⊤)

    ArrayBuilder′ : ∀ (A : tp+) n (m : Fin n → Bool) → tp+
    ArrayBuilder′ A n m = ArrayBuilder A n (tabulate m)

    module ArrayBuilder {A n} where
      empty : ArrayBuilder′ A n λ i → false
      empty = tabulate⁺ _

      assign : (i : Fin n) (a : A) → ArrayBuilder′ A n λ j → toℕ i == toℕ j
      assign i a = tabulate⁺ f
        module assign where
          f : ∀ j → if toℕ i == toℕ j then A else ⊤
          f j with toℕ i == toℕ j
          ...    | false = _
          ...    | true  = a

      seq : ∀ {m₁} (b₁ : ArrayBuilder A n m₁) {m₂} (b₂ : ArrayBuilder A n m₂) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
      seq {m₁} b₁ {m₂} b₂ = tabulate⁺ f
        module seq where
          f : ∀ i → if lookup m₁ i ∨ lookup m₂ i then A else ⊤
          f i with lookup m₁ i with lookup m₂ i with All.lookup i b₁ with All.lookup i b₂
          ...    | false          | false          | a₁                 | a₂ = _
          ...    | true           | false          | a₁                 | a₂ = a₁
          ...    | false          | true           | a₁                 | a₂ = a₂
          ...    | true           | true           | a₁                 | a₂ = a₂

      par : ∀ {m₁} (b₁ : ArrayBuilder A n m₁) {m₂} (b₂ : ArrayBuilder A n m₂) → M (ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i)
      par {m₁} b₁ {m₂} b₂ = Util.seq (Prod.tabulate f) >>= λ as → pure (tabulate⁺ (Prod.lookup as))
        module par where
          f : ∀ i → M (if lookup m₁ i ∨ lookup m₂ i then A else ⊤)
          f i with lookup m₁ i with lookup m₂ i with All.lookup i b₁ with All.lookup i b₂
          ...    | false          | false          | a₁                 | a₂ = pure _
          ...    | true           | false          | a₁                 | a₂ = pure a₁
          ...    | false          | true           | a₁                 | a₂ = pure a₂
          ...    | true           | true           | a₁                 | a₂ = branch >>= λ where
                                                                                 (lift false) → pure a₁
                                                                                 (lift true)  → pure a₂

      cast : ∀ {m m′} → (∀ i → m i ≡ m′ i) → ArrayBuilder′ A n m → ArrayBuilder′ A n m′
      cast eq = subst (ArrayBuilder A n) (tabulate-cong eq)

      cast′ : ∀ {m m′} → (∀ i → m i ≡ m′ i) → F (ArrayBuilder′ A n m) →⁻ F (ArrayBuilder′ A n m′)
      cast′ eq ._$⁻_ = subst (λ m → M (ArrayBuilder A n m)) (tabulate-cong eq)
      cast′ eq .$⁻-bind e = cast->>= (tabulate-cong eq)
        where
          cast->>= : ∀ {m m′} (eq : m ≡ m′) f → subst _ eq (e >>= f) ≡ e >>= λ b → subst _ eq (f b)
          cast->>= refl f = refl

      cast′-pure : ∀ {m m′} eq b → cast′ {m} {m′} eq $⁻ pure b ≡ pure (cast eq b)
      cast′-pure eq = cast-pure (tabulate-cong eq)
        where
          cast-pure : ∀ {m m′} (eq : m ≡ m′) b → subst _ eq (pure b) ≡ pure (subst _ eq b)
          cast-pure refl b = refl

      seq′ : ∀ {m₁} (b₁ : ArrayBuilder′ A n m₁) {m₂} (b₂ : ArrayBuilder′ A n m₂) → ArrayBuilder′ A n λ i → m₁ i ∨ m₂ i
      seq′ b₁ b₂ = cast (λ i → cong₂ _∨_ (lookup∘tabulate _ i) (lookup∘tabulate _ i)) (seq b₁ b₂)

      par′ : ∀ {m₁} (b₁ : ArrayBuilder′ A n m₁) {m₂} (b₂ : ArrayBuilder′ A n m₂) → M (ArrayBuilder′ A n λ i → m₁ i ∨ m₂ i)
      par′ b₁ b₂ = cast′ (λ i → cong₂ _∨_ (lookup∘tabulate _ i) (lookup∘tabulate _ i)) $⁻ par b₁ b₂

      par≡seq : ∀ {m₁} b₁ {m₂} b₂ → (∀ i → lookup m₁ i ≡ false ⊎ lookup m₂ i ≡ false) → par {m₁} b₁ {m₂} b₂ ≡ pure (seq b₁ b₂)
      par≡seq {m₁} b₁ {m₂} b₂ disjoint = begin
        Util.seq (Prod.tabulate par/f) >>= (λ as → pure (tabulate⁺ (Prod.lookup as)))                 ≡⟨ cong (λ es → Util.seq es >>= _) (Prod.tabulate-cong par/f≡seq/f) ⟩
        Util.seq (Prod.tabulate λ i → pure (seq/f i)) >>= (λ as → pure (tabulate⁺ (Prod.lookup as)))  ≡˘⟨ cong (λ es → Util.seq es >>= _) (Prod.map-tabulate _ seq/f) ⟩
        Util.seq (Prod.map pure (Prod.tabulate seq/f)) >>= (λ as → pure (tabulate⁺ (Prod.lookup as))) ≡⟨ cong (_>>= _) (Util.pure-seq _) ⟩
        pure (Prod.tabulate seq/f) >>= (λ as → pure (tabulate⁺ (Prod.lookup as)))                     ≡⟨ pure->>= _ _ ⟩
        pure (tabulate⁺ (Prod.lookup (Prod.tabulate seq/f)))                                          ≡⟨ cong pure (tabulate⁺-cong (Prod.lookup-tabulate seq/f)) ⟩
        pure (tabulate⁺ seq/f)                                                                        ∎
        where
          open par b₁ b₂ renaming (f to par/f)
          open seq b₁ b₂ renaming (f to seq/f)

          par/f≡seq/f : ∀ i → par/f i ≡ pure (seq/f i)
          par/f≡seq/f i with lookup m₁ i with lookup m₂ i with All.lookup i b₁ with All.lookup i b₂ with disjoint i
          ...              | false          | false          | a₁                 | a₂                 | _      = refl
          ...              | true           | false          | a₁                 | a₂                 | inj₂ _ = refl
          ...              | false          | true           | a₁                 | a₂                 | inj₁ _ = refl

      par′≡seq′ : ∀ {m₁} b₁ {m₂} b₂ → (∀ i → m₁ i ≡ false ⊎ m₂ i ≡ false) → par′ {m₁} b₁ {m₂} b₂ ≡ pure (seq′ b₁ b₂)
      par′≡seq′ b₁ b₂ disjoint = begin
        par′ b₁ b₂                  ≡⟨ cong (cast′ _ $⁻_) (par≡seq b₁ b₂ λ i → subst₂ (λ x y → x ≡ false ⊎ y ≡ false) (sym (lookup∘tabulate _ i)) (sym (lookup∘tabulate _ i)) (disjoint i)) ⟩
        cast′ _ $⁻ pure (seq b₁ b₂) ≡⟨ cast′-pure _ _ ⟩
        pure (seq′ b₁ b₂)           ∎

    Array : (A : tp+) (n : Nat) → tp+
    Array = Vec

    module Array {A n} where
      nth : (as : Array A n) (i : Fin n) → A
      nth = lookup

      build : (b : ArrayBuilder′ A n λ i → true) → Array A n
      build b = tabulate (tabulate⁻ b)

  module _ {ℓ″ ℂ costMonoid costMonad parCostMonoid} (parCostMonad : ParCostMonad {ℓ} {ℓ′} {ℓ″} {M} {ℂ} {monad} {costMonoid} costMonad parCostMonoid) where
    open CostMonad costMonad
    open ParCostMonad parCostMonad

    module Sig where
      private
        variable
          A : tp+
          n : Nat

      record ARRAY : Set (lsuc ℓ ⊔ lsuc ℓ′ ⊔ ℓ″) where
        field
          ArrayBuilder : ∀ (A : tp+) n (m : Vec Bool n) → tp-
          ArrayBuilder/ext : ∀ (u : ext) {m} → ArrayBuilder A n m ↔⁻ F (Spec.ArrayBuilder A n m)

        ArrayBuilder/ext/toSpec : ∀ (u : ext) {m} (b : U (ArrayBuilder A n m)) → M (Spec.ArrayBuilder A n m)
        ArrayBuilder/ext/toSpec u = ArrayBuilder/ext u .Inverse⁻.to ._$⁻_

        ArrayBuilder/ext/fromSpec : ∀ (u : ext) {m} (b : M (Spec.ArrayBuilder A n m)) → U (ArrayBuilder A n m)
        ArrayBuilder/ext/fromSpec u = ArrayBuilder/ext u .Inverse⁻.from ._$⁻_

        ArrayBuilder′ : ∀ (A : tp+) n (m : Fin n → Bool) → Set ℓ′
        ArrayBuilder′ A n m = U (ArrayBuilder A n (tabulate m))

        field
          ArrayBuilder/empty : ArrayBuilder′ A n λ i → false
          ArrayBuilder/empty/ext : ∀ u → ArrayBuilder/empty {A} {n} ≡ ArrayBuilder/ext/fromSpec u (pure Spec.ArrayBuilder.empty)

          ArrayBuilder/assign : ∀ i (a : A) → ArrayBuilder′ A n λ j → toℕ {n} i == toℕ j
          ArrayBuilder/assign/ext : ∀ u i a → ArrayBuilder/assign {A} {n} i a ≡ ArrayBuilder/ext/fromSpec u (pure (Spec.ArrayBuilder.assign i a))

          ArrayBuilder/seq : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          ArrayBuilder/seq/ext : ∀ u {m₁} b₁ {m₂} b₂ → ArrayBuilder/seq {A} {n} {m₁} b₁ {m₂} b₂ ≡ ArrayBuilder/ext/fromSpec u (ArrayBuilder/ext/toSpec u b₁ >>= λ b₁ → ArrayBuilder/ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))

          ArrayBuilder/par : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          ArrayBuilder/par/ext : ∀ u {m₁} b₁ {m₂} b₂ → ArrayBuilder/par {A} {n} {m₁} b₁ {m₂} b₂ ≡ ArrayBuilder/ext/fromSpec u ((ArrayBuilder/ext/toSpec u b₁ & ArrayBuilder/ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)

          Array : (A : tp+) (n : Nat) → tp+
          Array/ext : (u : ext) → Array A n ↔ Spec.Array A n

        Array/ext/toSpec : (u : ext) (as : Array A n) → Spec.Array A n
        Array/ext/toSpec u = Array/ext u .Inverse.to ._⟨$⟩_

        Array/ext/fromSpec : (u : ext) (as : Spec.Array A n) → Array A n
        Array/ext/fromSpec u = Array/ext u .Inverse.from ._⟨$⟩_

        field
          Array/nth : (as : Array A n) (i : Fin n) → M A
          Array/nth/ext : ∀ u as i → Array/nth {A} {n} as i ≡ pure (Spec.Array.nth (Array/ext/toSpec u as) i)

          Array/build : (b : ArrayBuilder′ A n λ i → true) → M (Array A n)
          Array/build/ext : ∀ u b → Array/build {A} {n} b ≡ ArrayBuilder/ext/toSpec u b >>= λ b → pure (Array/ext/fromSpec u (Spec.Array.build b))

        module ArrayBuilder {A n} where
          ext/toSpec : ∀ (u : ext) {m} (b : U (ArrayBuilder A n m)) → M (Spec.ArrayBuilder A n m)
          ext/toSpec = ArrayBuilder/ext/toSpec

          ext/fromSpec : ∀ (u : ext) {m} (b : M (Spec.ArrayBuilder A n m)) → U (ArrayBuilder A n m)
          ext/fromSpec = ArrayBuilder/ext/fromSpec

          ext/fromSpec-toSpec : ∀ u {m} b → ext/fromSpec u (ext/toSpec u {m} b) ≡ b
          ext/fromSpec-toSpec u = ArrayBuilder/ext u .Inverse⁻.left-inverse-of

          ext/toSpec-fromSpec : ∀ u {m} b → ext/toSpec u (ext/fromSpec u {m} b) ≡ b
          ext/toSpec-fromSpec u = ArrayBuilder/ext u .Inverse⁻.right-inverse-of

          ext/toSpec-bind : ∀ u {m B} e f → ext/toSpec u (bind (ArrayBuilder A n m) {B} e f) ≡ e >>= λ b → ext/toSpec u (f b)
          ext/toSpec-bind u = ArrayBuilder/ext u .Inverse⁻.to .$⁻-bind

          ext/fromSpec->>= : ∀ u {m B} e f → ext/fromSpec u (e >>= f) ≡ bind (ArrayBuilder A n m) {B} e λ b → ext/fromSpec u (f b)
          ext/fromSpec->>= u = ArrayBuilder/ext u .Inverse⁻.from .$⁻-bind

          empty : ArrayBuilder′ A n λ i → false
          empty = ArrayBuilder/empty

          empty/ext : ∀ u → empty ≡ ext/fromSpec u (pure Spec.ArrayBuilder.empty)
          empty/ext = ArrayBuilder/empty/ext

          ext/toSpec-empty : ∀ u → ext/toSpec u empty ≡ pure Spec.ArrayBuilder.empty
          ext/toSpec-empty u = begin
            ext/toSpec u empty                                           ≡⟨ cong (ext/toSpec u) (empty/ext u) ⟩
            ext/toSpec u (ext/fromSpec u (pure Spec.ArrayBuilder.empty)) ≡⟨ ext/toSpec-fromSpec u _ ⟩
            pure Spec.ArrayBuilder.empty                                 ∎

          assign : ∀ i (a : A) → ArrayBuilder′ A n λ j → toℕ {n} i == toℕ j
          assign = ArrayBuilder/assign

          assign/ext : ∀ u i a → assign i a ≡ ext/fromSpec u (pure (Spec.ArrayBuilder.assign i a))
          assign/ext = ArrayBuilder/assign/ext

          ext/toSpec-assign : ∀ u i a → ext/toSpec u (assign i a) ≡ pure (Spec.ArrayBuilder.assign i a)
          ext/toSpec-assign u i a = begin
            ext/toSpec u (assign i a)                                           ≡⟨ cong (ext/toSpec u) (assign/ext u i a) ⟩
            ext/toSpec u (ext/fromSpec u (pure (Spec.ArrayBuilder.assign i a))) ≡⟨ ext/toSpec-fromSpec u _ ⟩
            pure (Spec.ArrayBuilder.assign i a)                                 ∎

          seq : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          seq = ArrayBuilder/seq

          seq/ext : ∀ u {m₁} b₁ {m₂} b₂ → seq {m₁} b₁ {m₂} b₂ ≡ ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))
          seq/ext = ArrayBuilder/seq/ext

          ext/toSpec-seq : ∀ u {m₁} b₁ {m₂} b₂ → ext/toSpec u (seq {m₁} b₁ {m₂} b₂) ≡ ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂)
          ext/toSpec-seq u b₁ b₂ = begin
            ext/toSpec u (seq b₁ b₂)                                                                                                 ≡⟨ cong (ext/toSpec u) (seq/ext u b₁ b₂) ⟩
            ext/toSpec u (ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))) ≡⟨ ext/toSpec-fromSpec u _ ⟩
            ext/toSpec u b₁ >>= (λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))                               ∎

          par : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          par = ArrayBuilder/par

          par/ext : ∀ u {m₁} b₁ {m₂} b₂ → par {m₁} b₁ {m₂} b₂ ≡ ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)
          par/ext = ArrayBuilder/par/ext

          ext/toSpec-par : ∀ u {m₁} b₁ {m₂} b₂ → ext/toSpec u (par {m₁} b₁ {m₂} b₂) ≡ (ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂
          ext/toSpec-par u b₁ b₂ = begin
            ext/toSpec u (par b₁ b₂)                                                                                          ≡⟨ cong (ext/toSpec u) (par/ext u b₁ b₂) ⟩
            ext/toSpec u (ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)) ≡⟨ ext/toSpec-fromSpec u _ ⟩
            (ext/toSpec u b₁ & ext/toSpec u b₂) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)                               ∎

          cast : ∀ {m m′} → (∀ i → m i ≡ m′ i) → ArrayBuilder′ A n m → ArrayBuilder′ A n m′
          cast eq = subst (λ m → U (ArrayBuilder A n m)) (tabulate-cong eq)

          ext/toSpec-cast : ∀ u {m m′} eq b → ext/toSpec u (cast {m} {m′} eq b) ≡ Spec.ArrayBuilder.cast′ eq $⁻ ext/toSpec u b
          ext/toSpec-cast u eq = toSpec-cast (tabulate-cong eq)
            where
              toSpec-cast : ∀ {m m′} (eq : m ≡ m′) b → ext/toSpec u (subst _ eq b) ≡ subst _ eq (ext/toSpec u b)
              toSpec-cast refl b = refl

          cast-ext/fromSpec : ∀ u {m m′} eq b → cast {m} {m′} eq (ext/fromSpec u b) ≡ ext/fromSpec u (Spec.ArrayBuilder.cast′ eq $⁻ b)
          cast-ext/fromSpec u eq = cast-fromSpec (tabulate-cong eq)
            where
              cast-fromSpec : ∀ {m m′} (eq : m ≡ m′) b → subst _ eq (ext/fromSpec u b) ≡ ext/fromSpec u (subst _ eq b)
              cast-fromSpec refl b = refl

          seq′ : ∀ {m₁} (b₁ : ArrayBuilder′ A n m₁) {m₂} (b₂ : ArrayBuilder′ A n m₂) → ArrayBuilder′ A n λ i → m₁ i ∨ m₂ i
          seq′ b₁ b₂ = cast (λ i → cong₂ _∨_ (lookup∘tabulate _ i) (lookup∘tabulate _ i)) (seq b₁ b₂)

          seq′/ext : ∀ u {m₁} b₁ {m₂} b₂ → seq′ {m₁} b₁ {m₂} b₂ ≡ ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq′ b₁ b₂))
          seq′/ext u b₁ b₂ = begin
            cast _ (seq b₁ b₂)                                                                                                                       ≡⟨ cong (cast _) (seq/ext u b₁ b₂) ⟩
            cast _ (ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂)))                       ≡⟨ cast-ext/fromSpec u _ _ ⟩
            ext/fromSpec u (Spec.ArrayBuilder.cast′ _ $⁻ (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))) ≡⟨ cong (ext/fromSpec u) (Spec.ArrayBuilder.cast′ _ .$⁻-bind _ _) ⟩
            ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → Spec.ArrayBuilder.cast′ _ $⁻ (ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))) ≡⟨ cong (ext/fromSpec u) (>>=-cong _ λ b₁ → Spec.ArrayBuilder.cast′ _ .$⁻-bind _ _) ⟩
            ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → Spec.ArrayBuilder.cast′ _ $⁻ pure (Spec.ArrayBuilder.seq b₁ b₂))   ≡⟨ cong (ext/fromSpec u) (>>=-cong _ λ b₁ → >>=-cong _ λ b₂ → Spec.ArrayBuilder.cast′-pure _ _) ⟩
            ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq′ b₁ b₂))                               ∎

          ext/toSpec-seq′ : ∀ u {m₁} b₁ {m₂} b₂ → ext/toSpec u (seq′ {m₁} b₁ {m₂} b₂) ≡ ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq′ b₁ b₂)
          ext/toSpec-seq′ u b₁ b₂ = begin
            ext/toSpec u (seq′ b₁ b₂)                                                                                                 ≡⟨ cong (ext/toSpec u) (seq′/ext u b₁ b₂) ⟩
            ext/toSpec u (ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq′ b₁ b₂))) ≡⟨ ext/toSpec-fromSpec u _ ⟩
            ext/toSpec u b₁ >>= (λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq′ b₁ b₂))                               ∎

          par′ : ∀ {m₁} (b₁ : ArrayBuilder′ A n m₁) {m₂} (b₂ : ArrayBuilder′ A n m₂) → ArrayBuilder′ A n λ i → m₁ i ∨ m₂ i
          par′ b₁ b₂ = cast (λ i → cong₂ _∨_ (lookup∘tabulate _ i) (lookup∘tabulate _ i)) (par b₁ b₂)

          par′/ext : ∀ u {m₁} b₁ {m₂} b₂ → par′ {m₁} b₁ {m₂} b₂ ≡ ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂)
          par′/ext u b₁ b₂ = begin
            cast _ (par b₁ b₂)                                                                                                                ≡⟨ cong (cast _) (par/ext u b₁ b₂) ⟩
            cast _ (ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂))                       ≡⟨ cast-ext/fromSpec u _ _ ⟩
            ext/fromSpec u (Spec.ArrayBuilder.cast′ _ $⁻ ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)) ≡⟨ cong (ext/fromSpec u) (Spec.ArrayBuilder.cast′ _ .$⁻-bind _ _) ⟩
            ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂)                               ∎

          ext/toSpec-par′ : ∀ u {m₁} b₁ {m₂} b₂ → ext/toSpec u (par′ {m₁} b₁ {m₂} b₂) ≡ (ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂
          ext/toSpec-par′ u b₁ b₂ = begin
            ext/toSpec u (par′ b₁ b₂)                                                                                          ≡⟨ cong (ext/toSpec u) (par′/ext u b₁ b₂) ⟩
            ext/toSpec u (ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂)) ≡⟨ ext/toSpec-fromSpec u _ ⟩
            (ext/toSpec u b₁ & ext/toSpec u b₂) >>= (λ (b₁ , b₂) → Spec.ArrayBuilder.par′ b₁ b₂)                               ∎

        module Array {A n} where
          ext/toSpec : (u : ext) (as : Array A n) → Spec.Array A n
          ext/toSpec = Array/ext/toSpec

          ext/fromSpec : (u : ext) (as : Spec.Array A n) → Array A n
          ext/fromSpec = Array/ext/fromSpec

          ext/fromSpec-toSpec : ∀ u as → ext/fromSpec u (ext/toSpec u as) ≡ as
          ext/fromSpec-toSpec u = Array/ext u .Inverse.left-inverse-of

          ext/toSpec-fromSpec : ∀ u as → ext/toSpec u (ext/fromSpec u as) ≡ as
          ext/toSpec-fromSpec u = Array/ext u .Inverse.right-inverse-of

          nth : (as : Array A n) (i : Fin n) → M A
          nth = Array/nth

          nth/ext : ∀ u as i → nth as i ≡ pure (Spec.Array.nth (ext/toSpec u as) i)
          nth/ext = Array/nth/ext

          build : (b : ArrayBuilder′ A n λ i → true) → M (Array A n)
          build = Array/build

          build/ext : ∀ u b → build b ≡ ArrayBuilder/ext/toSpec u b >>= λ b → pure (ext/fromSpec u (Spec.Array.build b))
          build/ext = Array/build/ext

    module Imp (arrayStep : ArrayStep → ℂ) where
      open Sig
      open ARRAY

      array : ARRAY

      array .ArrayBuilder = _
      array .ArrayBuilder/ext u = Inverse⁻.id

      array .ArrayBuilder/empty = _
      array .ArrayBuilder/empty/ext u = refl

      array .ArrayBuilder/assign = _
      array .ArrayBuilder/assign/ext u i a = ext/step->> u (arrayStep (write i a)) _

      array .ArrayBuilder/seq = _
      array .ArrayBuilder/seq/ext u b₁ b₂ = refl

      array .ArrayBuilder/par b₁ b₂ = _
      array .ArrayBuilder/par/ext u b₁ b₂ = refl

      array .Array = _
      array .Array/ext u = id

      array .Array/nth = _
      array .Array/nth/ext u as i = ext/step->> u (arrayStep (read as i)) _

      array .Array/build = _
      array .Array/build/ext {A} {n} u b = ext/step->> u (arrayStep (alloc A n)) _

      open ARRAY array public
