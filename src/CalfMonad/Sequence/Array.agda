{-# OPTIONS --cubical-compatible --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.Monad
open import CalfMonad.NondetMonad

open import CalfMonad.Sequence.ArrayCostMonoid

module CalfMonad.Sequence.Array {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid} (parCostMonad : ParCostMonad {ℓ} {ℓ′} {ℓ″} {M} {ℂ} {monad} {costMonoid} costMonad parCostMonoid) (arrayCostMonoid : ArrayCostMonoid ℓ ℂ) (nondetMonad : NondetMonad M) where

open Monad monad
open CostMonad costMonad
open ParCostMonad parCostMonad
open ArrayCostMonoid arrayCostMonoid
open NondetMonad nondetMonad

open import Agda.Builtin.Sigma
open import Data.Bool.Base                             using (Bool; _∨_; false; true)
open import Data.Fin.Base                              using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties                        using (_≟_; fromℕ<-toℕ; toℕ<n)
open import Data.Nat.Base                              using (_<‴_; _≤_; suc; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties                        using (+-cancelˡ-≤; <⇒≤; ≤-refl; ≤‴⇒≤; ≤⇒≤‴)
open import Data.Unit.Polymorphic                      using (⊤)
open import Data.Vec.Base                              using (Vec; lookup; tabulate)
open import Data.Vec.Properties                        using (lookup∘tabulate)
open import Data.Vec.Relation.Unary.All as All         using (All)
open import Function.Base                              using (_$_; case_of_)
open import Level                                      using (lift)
open import Relation.Binary.PropositionalEquality.Core using (subst; sym)
open import Relation.Nullary                           using (does)

open import CalfMonad.CBPV monad

open import CalfMonad.Sequence.ArraySig monad

private
  Init : Set ℓ → Bool → Set ℓ
  Init A false = ⊤
  Init A true  = A

  tabulate′ : ∀ {A : Set} {P : A → Set ℓ} {n} {f : Fin n → A} → (∀ i → P (f i)) → All P (tabulate f)
  tabulate′ {P = P} g = All.tabulate λ i → subst P (sym $ lookup∘tabulate _ i) $ g i

open ARRAY

array : ARRAY
array .Array = Vec
array .ArrayBuilder A n m = F (All (Init A) m)

array .nth as i = do
  step $ arrayStep $ read as i
  pure $ lookup as i

array .empty = pure $ tabulate′ _

array .assign i a = do
  step $ arrayStep $ write i a
  pure $ tabulate′ assign′
  where
    assign′ : ∀ j → Init _ (does (i ≟ j))
    assign′ j with does (i ≟ j)
    ...          | false = _
    ...          | true  = a

array .seq {m₁ = m₁} b₁ {m₂} b₂ = do
  b₁ ← b₁
  b₂ ← b₂
  pure $ tabulate′ λ i → seq′ i (All.lookup i b₁) (All.lookup i b₂)
  where
    seq′ : ∀ i → Init _ (lookup m₁ i) → Init _ (lookup m₂ i) → Init _ (lookup m₂ i ∨ lookup m₁ i)
    seq′ i a₁ a₂ with lookup m₁ i with lookup m₂ i
    ...             | false          | false = _
    ...             | true           | false = a₁
    ...             | _              | true  = a₂

array .par {n = n} {m₁} b₁ {m₂} b₂ = do
  b₁ , b₂ ← b₁ & b₂
  b ← par′ b₁ b₂ n ≤-refl
  pure $ tabulate′ λ i → b i $ ≤⇒≤‴ $ toℕ<n i
  where
    par″ : ∀ i → Init _ (lookup m₁ i) → Init _ (lookup m₂ i) → M (Init _ (lookup m₁ i ∨ lookup m₂ i))
    par″ i a₁ a₂ with lookup m₁ i with lookup m₂ i
    ...             | false          | false = pure _
    ...             | true           | false = pure a₁
    ...             | false          | true  = pure a₂
    ...             | true           | true  = branch >>= λ where
                                                 (lift false) → pure a₁
                                                 (lift true)  → pure a₂

    par′ : All (Init _) m₁ → All (Init _) m₂ → ∀ i → i ≤ n → M (∀ j → toℕ j <‴ i → Init _ (lookup m₁ j ∨ lookup m₂ j))
    par′ b₁ b₂ 0 le = pure λ j lt → case ≤‴⇒≤ lt of λ ()
    par′ b₁ b₂ (suc i) le = do
      b ← par′ b₁ b₂ i $ <⇒≤ le
      a ← par″ (fromℕ< le) (All.lookup _ b₁) (All.lookup _ b₂)
      pure λ where
        j ≤‴-refl → subst (λ k → Init _ (lookup m₁ k ∨ lookup m₂ k)) (fromℕ<-toℕ j le) a
        j (≤‴-step lt) → b j $ ≤⇒≤‴ $ +-cancelˡ-≤ 1 $ ≤‴⇒≤ lt

array .build {A} {n} b = do
  step $ arrayStep $ alloc A n
  b ← b
  pure $ tabulate λ i → subst (Init A) (lookup∘tabulate _ i) $ All.lookup i b
