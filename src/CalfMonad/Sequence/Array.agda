{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Sequence.Array ℓ where

open Agda.Primitive
open import Agda.Builtin.Nat
open import Data.Bool.Base                                  using (Bool; _∨_; false; if_then_else_; true)
open import Data.Fin.Base                                   using (Fin)
open import Data.Fin.Properties                             using (_≟_)
open import Data.List.Relation.Unary.All.Properties as LAll using ()
open import Data.Product                                    using (_×_; _,_)
open import Data.Unit.Polymorphic.Base                      using (⊤)
open import Data.Vec.Base                                   using (Vec; lookup; tabulate)
open import Data.Vec.Relation.Unary.All             as All  using (All)
open import Data.Vec.Relation.Unary.All.Properties          using (tabulate⁺; tabulate⁻)
open import Function.Equality                               using (_⟨$⟩_)
open import Function.Inverse                                using (Inverse; _↔_; id)
open import Level                                           using (lift)
open import Relation.Binary.PropositionalEquality.Core      using (_≡_; refl; subst; sym)
open import Relation.Nullary.Decidable.Core                 using (⌊_⌋)

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoids
open import CalfMonad.Monad
open import CalfMonad.NondetMonad

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

  open import CalfMonad.CBPV monad

  module Spec where
    ArrayBuilder : ∀ (A : tp+) n (m : Vec Bool n) → tp+
    ArrayBuilder A n = All (if_then A else ⊤)

    ArrayBuilder′ : ∀ (A : tp+) n (m : Fin n → Bool) → tp+
    ArrayBuilder′ A n m = ArrayBuilder A n (tabulate m)

    module ArrayBuilder {A n} where
      empty : ArrayBuilder′ A n λ i → false
      empty = tabulate⁺ _

      assign : ∀ i (a : A) → ArrayBuilder′ A n λ j → ⌊ i ≟ j ⌋
      assign i a = tabulate⁺ f
        where
          f : ∀ j → if ⌊ i ≟ j ⌋ then A else ⊤
          f j with ⌊ i ≟ j ⌋
          ...    | false = _
          ...    | true  = a

      seq : ∀ {m₁} (b₁ : ArrayBuilder A n m₁) {m₂} (b₂ : ArrayBuilder A n m₂) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
      seq {m₁} b₁ {m₂} b₂ = tabulate⁺ f
        where
          f : ∀ i → if lookup m₁ i ∨ lookup m₂ i then A else ⊤
          f i with lookup m₁ i with lookup m₂ i with All.lookup i b₁ with All.lookup i b₂
          ...    | false          | false          | a₁                 | a₂ = _
          ...    | true           | false          | a₁                 | a₂ = a₁
          ...    | false          | true           | a₁                 | a₂ = a₂
          ...    | true           | true           | a₁                 | a₂ = a₂

      par : ∀ {m₁} (b₁ : ArrayBuilder A n m₁) {m₂} (b₂ : ArrayBuilder A n m₂) → M (ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i)
      par {m₁} b₁ {m₂} b₂ = seqbind (F _) (LAll.tabulate⁺ f) λ as → pure (tabulate⁺ (LAll.tabulate⁻ as))
        where
          f : ∀ i → M (if lookup m₁ i ∨ lookup m₂ i then A else ⊤)
          f i with lookup m₁ i with lookup m₂ i with All.lookup i b₁ with All.lookup i b₂
          ...    | false          | false          | a₁                 | a₂ = pure _
          ...    | true           | false          | a₁                 | a₂ = pure a₁
          ...    | false          | true           | a₁                 | a₂ = pure a₂
          ...    | true           | true           | a₁                 | a₂ = branch >>= λ where
                                                                                 (lift false) → pure a₁
                                                                                 (lift true)  → pure a₂
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
          ArrayBuilder/ext : ∀ (u : ext) {m} → U (ArrayBuilder A n m) ↔ M (Spec.ArrayBuilder A n m) -- TODO: equiv as tp-

        ArrayBuilder/ext/toSpec : ∀ (u : ext) {m} (b : U (ArrayBuilder A n m)) → M (Spec.ArrayBuilder A n m)
        ArrayBuilder/ext/toSpec u = ArrayBuilder/ext u .Inverse.to ⟨$⟩_

        ArrayBuilder/ext/fromSpec : ∀ (u : ext) {m} (b : M (Spec.ArrayBuilder A n m)) → U (ArrayBuilder A n m)
        ArrayBuilder/ext/fromSpec u = ArrayBuilder/ext u .Inverse.from ⟨$⟩_

        ArrayBuilder′ : ∀ (A : tp+) n (m : Fin n → Bool) → Set ℓ′
        ArrayBuilder′ A n m = U (ArrayBuilder A n (tabulate m))

        field
          ArrayBuilder/empty : ArrayBuilder′ A n λ i → false
          ArrayBuilder/empty/ext : ∀ u → ArrayBuilder/empty {A} {n} ≡ ArrayBuilder/ext/fromSpec u (pure Spec.ArrayBuilder.empty)

          ArrayBuilder/assign : ∀ i (a : A) → ArrayBuilder′ A n λ j → ⌊ i ≟ j ⌋
          ArrayBuilder/assign/ext : ∀ u i a → ArrayBuilder/assign {A} {n} i a ≡ ArrayBuilder/ext/fromSpec u (pure (Spec.ArrayBuilder.assign i a))

          ArrayBuilder/seq : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          ArrayBuilder/seq/ext : ∀ u {m₁} b₁ {m₂} b₂ → ArrayBuilder/seq {A} {n} {m₁} b₁ {m₂} b₂ ≡ ArrayBuilder/ext/fromSpec u (ArrayBuilder/ext/toSpec u b₁ >>= λ b₁ → ArrayBuilder/ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))

          ArrayBuilder/par : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          ArrayBuilder/par/ext : ∀ u {m₁} b₁ {m₂} b₂ → ArrayBuilder/par {A} {n} {m₁} b₁ {m₂} b₂ ≡ ArrayBuilder/ext/fromSpec u ((ArrayBuilder/ext/toSpec u b₁ & ArrayBuilder/ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)

          Array : (A : tp+) (n : Nat) → tp+
          Array/ext : (u : ext) → Array A n ↔ Spec.Array A n

        Array/ext/toSpec : (u : ext) (as : Array A n) → Spec.Array A n
        Array/ext/toSpec u = Array/ext u .Inverse.to ⟨$⟩_

        Array/ext/fromSpec : (u : ext) (as : Spec.Array A n) → Array A n
        Array/ext/fromSpec u = Array/ext u .Inverse.from ⟨$⟩_

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
          ext/fromSpec-toSpec u = ArrayBuilder/ext u .Inverse.left-inverse-of

          ext/toSpec-fromSpec : ∀ u {m} b → ext/toSpec u (ext/fromSpec u {m} b) ≡ b
          ext/toSpec-fromSpec u = ArrayBuilder/ext u .Inverse.right-inverse-of

          empty : ArrayBuilder′ A n λ i → false
          empty = ArrayBuilder/empty

          empty/ext : ∀ u → empty ≡ ext/fromSpec u (pure Spec.ArrayBuilder.empty)
          empty/ext = ArrayBuilder/empty/ext

          assign : ∀ i (a : A) → ArrayBuilder′ A n λ j → ⌊ i ≟ j ⌋
          assign = ArrayBuilder/assign

          assign/ext : ∀ u i a → assign i a ≡ ext/fromSpec u (pure (Spec.ArrayBuilder.assign i a))
          assign/ext = ArrayBuilder/assign/ext

          seq : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          seq = ArrayBuilder/seq

          seq/ext : ∀ u {m₁} b₁ {m₂} b₂ → seq {m₁} b₁ {m₂} b₂ ≡ ext/fromSpec u (ext/toSpec u b₁ >>= λ b₁ → ext/toSpec u b₂ >>= λ b₂ → pure (Spec.ArrayBuilder.seq b₁ b₂))
          seq/ext = ArrayBuilder/seq/ext

          par : ∀ {m₁} (b₁ : U (ArrayBuilder A n m₁)) {m₂} (b₂ : U (ArrayBuilder A n m₂)) → ArrayBuilder′ A n λ i → lookup m₁ i ∨ lookup m₂ i
          par = ArrayBuilder/par

          par/ext : ∀ u {m₁} b₁ {m₂} b₂ → par {m₁} b₁ {m₂} b₂ ≡ ext/fromSpec u ((ext/toSpec u b₁ & ext/toSpec u b₂) >>= λ (b₁ , b₂) → Spec.ArrayBuilder.par b₁ b₂)
          par/ext = ArrayBuilder/par/ext

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

      array .ArrayBuilder A n m = F _
      array .ArrayBuilder/ext u = id

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
