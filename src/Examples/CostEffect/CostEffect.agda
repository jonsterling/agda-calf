{-# OPTIONS --prop --without-K --rewriting #-}

-- This module extends the CBPV metalanguage with effects corresponding to computational steps.

open import Calf.CostMonoid
open import Calf.CostMonoids

module Examples.CostEffect.CostEffect (costMonoid : CostMonoid) where
open CostMonoid costMonoid
open import Calf.Prelude
open import Calf.Metalanguage
open import Calf.Step costMonoid
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
open import Data.Nat
open import Calf.Types.Nat
open import Calf.Types.Sum

-- I am a little less scared of this version.
postulate
  ► : (c : ℂ) → tp pos → tp pos
  ►/ret : ∀ c A → val A → val (► c A)
  ►/match : ∀ {c A} X → val (► c A) → (val A → cmp X) → cmp X
  ►/match/ret : ∀ {c A X} {u : val A} {f : val A → cmp X} → ►/match X (►/ret c A u) f ≡ step' X c (f u)
  {-# REWRITE ►/match/ret #-}

-- I don't know the above is strong enough, but at least it seems not
-- too strong lol.  The thing I am struggling with is, I basically
-- want some kind of abstract type in the LF that forces you to take a
-- step, but I don't want you to be able to extract the thing that
-- takes that step internally. That's why this is not really the same
-- as the refinement that you get by looking at the image of "step".
postulate
  ▷ : (c : ℂ) → tp neg → tp neg
  ▷/ret : ∀ c X → cmp X → cmp (▷ c X)
  ▷/match : ∀ {c X} Y → cmp (▷ c X) → (cmp X → cmp Y) → cmp Y
  ▷/match/ret : ∀ {c X Y} {e : cmp X} {f : cmp X → cmp Y} → ▷/match Y (▷/ret c X e) f ≡ step' Y c (f e)
  {-# REWRITE ▷/match/ret #-}

-- Experiments with a cost-aware list type
-- postulate
--   L* : (c : ℂ) → tp pos → tp pos

-- data L (c : ℂ) (A : tp pos) : Set where
--   nil : L c A
--   cons : (a : val A) → val (► c (L* c A)) → L c A

-- postulate
--   L*/decode : ∀ {c A} → val (L* c A) ≡ L c A
--   {-# REWRITE L*/decode #-}

-- fails termination check...
-- L1 = L* 1 nat
-- rev/helper : cmp (Π L1 λ _ → Π L1 λ _ → F L1)
-- rev/helper nil = λ a → ret a
-- rev/helper (cons a x) =
--   ►/match (Π L1 (λ _ → F L1))
--   x
--   λ l → λ l' → (rev/helper l) (cons a (►/ret 1 L1 l'))
