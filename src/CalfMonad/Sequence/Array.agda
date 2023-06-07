{-# OPTIONS --cubical-compatible --lossy-unification --safe #-}

open import CalfMonad.CostMonad
open import CalfMonad.CostMonoid
open import CalfMonad.Monad
open import CalfMonad.NondetMonad

open import CalfMonad.Sequence.ArrayCostMonoid

module CalfMonad.Sequence.Array {ℓ} {M : Set → Set} {ℂ : Set ℓ} {monad : Monad M} {costMonoid : CostMonoid ℂ} {costMonad : CostMonad monad costMonoid} {parCostMonoid : ParCostMonoid ℂ} (parCostMonad : ParCostMonad costMonad parCostMonoid) (arrayCostMonoid : ArrayCostMonoid monad ℂ) (nondetMonad : NondetMonad M) where

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
open import Data.Vec.Base                              using (lookup; tabulate)
open import Data.Vec.Properties                        using (lookup∘tabulate)
open import Function.Base                              using (_$_; case_of_)
open import Function.Equality                          using (_⟨$⟩_)
open import Function.Equivalence                       using (Equivalence)
open import Level                                      using (lift)
open import Relation.Binary.PropositionalEquality.Core using (subst; sym)
open import Relation.Nullary                           using (yes)

open import CalfMonad.CBPV monad
open import CalfMonad.CBPV.Types.Vec monad

open import CalfMonad.Sequence.ArraySig monad

open ARRAY

Array : ARRAY
Array .array = vec
Array .arrayBuilder A n m = F $ meta ∀ i → T (lookup m i) → val A

Array .nth n as i = do
  step $ arrayStep $ read as i
  pure $ lookup as i

Array .empty n = do
  pure λ i p → case subst T (lookup∘tabulate _ i) p of λ ()

Array .assign n i a = do
  step $ arrayStep $ write i a
  pure λ j p → a

Array .seq n m₁ b₁ m₂ b₂ = do
  b₁ ← b₁
  b₂ ← b₂
  pure λ i p → [ b₂ i , b₁ i ] $ Equivalence.to T-∨ ⟨$⟩ subst T (lookup∘tabulate _ i) p

Array .par {A} n m₁ b₁ m₂ b₂ = do
  b₁ , b₂ ← b₁ & b₂
  b ← par′ b₁ b₂ n ≤-refl
  pure λ i p → b i (≤⇒≤‴ (toℕ<n i)) $ subst T (lookup∘tabulate _ i) p
  where
    par′ : (∀ i → T (lookup m₁ i) → val A) → (∀ i → T (lookup m₂ i) → val A) → ∀ i → i ≤ n → M (∀ j → toℕ j <‴ i → T (lookup m₁ j ∨ lookup m₂ j) → val A)
    par′ b₁ b₂ 0 le = pure λ j le′ → case ≤‴⇒≤ le′ of λ ()
    par′ b₁ b₂ (suc i) le = do
      b ← par′ b₁ b₂ i (<⇒≤ le)
      let i′ = fromℕ< le
      a ← case T? (lookup m₁ i′) ,′ T? (lookup m₂ i′) of λ where
        (yes p₁ , yes p₂) → branch >>= λ where
          (lift false) → pure λ p → b₁ i′ p₁
          (lift true)  → pure λ p → b₂ i′ p₂
        _ → pure λ p → [ b₁ i′ , b₂ i′ ] $ Equivalence.to T-∨ ⟨$⟩ p
      pure λ where
        j ≤‴-refl p → a (subst (λ i′ → T (lookup m₁ i′ ∨ lookup m₂ i′)) (sym (fromℕ<-toℕ j le)) p)
        j (≤‴-step le′) p → b j (≤⇒≤‴ $ +-cancelˡ-≤ 1 $ ≤‴⇒≤ le′) p

Array .build {A} n b = do
  step $ arrayStep $ alloc A n
  b ← b
  pure $ tabulate λ i → b i $ subst T (sym $ lookup∘tabulate _ i) _
