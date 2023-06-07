{-# OPTIONS --cubical-compatible --lossy-unification --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad
open import CalfMonad.NondetMonad

open import CalfMonad.Sequence.ArrayCostMonoid

module CalfMonad.Sequence.Array {ℓ M ℂ monad costMonoid costMonad parCostMonoid} (parCostMonad : ParCostMonad {_} {_} {ℓ} {M} {ℂ} {monad} {costMonoid} costMonad parCostMonoid) (arrayCostMonoid : ArrayCostMonoid ℂ) (nondetMonad : NondetMonad M) where

open Monad monad
open CostMonad costMonad
open ParCostMonad parCostMonad
open ArrayCostMonoid arrayCostMonoid
open NondetMonad nondetMonad

open import Data.Bool.Base                             using (T; _∨_; false; true)
open import Data.Bool.Properties                       using (T-∨; T?)
open import Data.Fin.Base                              using (fromℕ<; toℕ)
open import Data.Fin.Properties                        using (fromℕ<-toℕ; toℕ<n)
open import Data.Nat.Base                              using (_<‴_; _≤_; suc; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties                        using (+-cancelˡ-≤; <⇒≤; ≤-refl; ≤‴⇒≤; ≤⇒≤‴)
open import Data.Product                               using (_,_; _,′_)
open import Data.Sum.Base                              using ([_,_])
open import Data.Vec.Base                              using (Vec; lookup; tabulate)
open import Data.Vec.Properties                        using (lookup∘tabulate)
open import Function.Base                              using (_$_; case_of_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Equivalence                       using (Equivalence)
open import Level                                      using (lift)
open import Relation.Binary.PropositionalEquality.Core using (subst; sym)
open import Relation.Nullary                           using (yes)

open import CalfMonad.CBPV monad

open import CalfMonad.Sequence.ArraySig monad

open ARRAY

array : ARRAY
array .Array = Vec
array .ArrayBuilder A n m = F ∀ i → T (lookup m i) → A

array .nth as i = do
  step $ arrayStep $ read as i
  pure $ lookup as i

array .empty = do
  pure λ i p → case subst T (lookup∘tabulate _ i) p of λ ()

array .assign i a = do
  step $ arrayStep $ write i a
  pure λ j p → a

array .seq b₁ b₂ = do
  b₁ ← b₁
  b₂ ← b₂
  pure λ i p → [ b₂ i , b₁ i ] $ Equivalence.to T-∨ ⟨$⟩ subst T (lookup∘tabulate _ i) p

array .par {A} {n} {m₁} b₁ {m₂} b₂ = do
  b₁ , b₂ ← b₁ & b₂
  par′ b₁ b₂
  where
    par′ : (∀ _ → _ → A) → (∀ _ → _ → A) → _
    par′ b₁ b₂ = do
      b ← par″ n ≤-refl
      pure λ i p → b i (≤⇒≤‴ $ toℕ<n i) $ subst T (lookup∘tabulate _ i) p
      where
        par″ : ∀ i → i ≤ n → M (∀ j → toℕ j <‴ i → T (lookup m₁ j ∨ lookup m₂ j) → A)
        par″ 0 le = pure λ j le′ → case ≤‴⇒≤ le′ of λ ()
        par″ (suc i) le = do
          b ← par″ i (<⇒≤ le)
          let i′ = fromℕ< le
          a ← case T? (lookup m₁ i′) ,′ T? (lookup m₂ i′) of λ where
            (yes p₁ , yes p₂) → branch >>= λ where
              (lift false) → pure λ p → b₁ i′ p₁
              (lift true)  → pure λ p → b₂ i′ p₂
            _ → pure λ p → [ b₁ i′ , b₂ i′ ] $ Equivalence.to T-∨ ⟨$⟩ p
          pure λ where
            j ≤‴-refl p → a $ subst (λ i′ → T (lookup m₁ i′ ∨ lookup m₂ i′)) (sym $ fromℕ<-toℕ j le) p
            j (≤‴-step le′) p → b j (≤⇒≤‴ $ +-cancelˡ-≤ 1 $ ≤‴⇒≤ le′) p

array .build {A} {n} b = do
  step $ arrayStep $ alloc A n
  b ← b
  pure $ tabulate λ i → b i $ subst T (sym $ lookup∘tabulate _ i) _
