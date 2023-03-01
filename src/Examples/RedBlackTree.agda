{-# OPTIONS --prop --rewriting #-}

module Examples.RedBlackTree where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Level using (0ℓ)

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool
open import Calf.Types.Product
open import Calf.Types.Nat
-- open import Data.Nat as Nat using (_+_)
open import Data.Nat.Properties as Nat

open import Relation.Nullary
open import Relation.Binary
-- open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)


module RedBlackTree (STO : StrictTotalOrder 0ℓ 0ℓ 0ℓ) where
  open StrictTotalOrder STO

  A : tp pos
  A = U (meta Carrier)

  data RBT : Set where
    leaf  : RBT
    red   : (a : val A) (t₁ t₂ : RBT) → RBT
    black : (a : val A) (t₁ t₂ : RBT)→ RBT
  rbt : tp pos
  rbt = U (meta RBT)

  split : cmp (Π rbt λ _ → Π A λ _ → F (prod bool (prod rbt rbt)))
  join : cmp (Π rbt λ _ → Π rbt λ _ → F rbt)

  split leaf a = ret (false , leaf , leaf)
  split (red a' t₁ t₂) a with compare a a'
  ... | tri< a<a' ¬a≡a' ¬a>a' =
          bind (F (prod bool (prod rbt rbt))) (split t₁ a) λ ( b , t₁₁ , t₁₂ ) →
          bind (F (prod bool (prod rbt rbt))) (join t₁₂ t₂) λ t →
          step (F (prod bool (prod rbt rbt))) (1 , 1) (ret (b , t₁₁ , t))
  ... | tri≈ ¬a<a' a≡a' ¬a>a' = ret (true , t₁ , t₂)
  ... | tri> ¬a<a' ¬a≡a' a>a' = {!   !}
  split (black a' t₁ t₂) a with compare a a'
  ... | tri< a<a' ¬a≡a' ¬a>a' = {!   !}
  ... | tri≈ ¬a<a' a≡a' ¬a>a' = ret (true , t₁ , t₂)
  ... | tri> ¬a<a' ¬a≡a' a>a' = {!   !}

  join leaf t₂ = ret t₂
  join (red a t₁₁ t₁₂) t₂ = {!   !}
  join (black a t₁₁ t₁₂) t₂ = {!   !}


  empty : cmp (F rbt)
  empty = ret leaf

  singleton : cmp (Π A λ _ → F rbt)
  singleton a = ret (red a leaf leaf)

  find : cmp (Π rbt λ _ → Π A λ _ → F bool)
  find t a = bind (F bool) (split t a) λ { (b , _) → ret b }


module _ where
  open RedBlackTree Nat.<-strictTotalOrder

  example : cmp (F (prod bool (prod rbt rbt)))
  example =
    bind (F (prod bool (prod rbt rbt))) (singleton 1) λ t₁ →
    bind (F (prod bool (prod rbt rbt))) (singleton 2) λ t₂ →
    bind (F (prod bool (prod rbt rbt))) (singleton 3) λ t₃ →
    bind (F (prod bool (prod rbt rbt))) (join t₁ t₂) λ t₁₂ →
    bind (F (prod bool (prod rbt rbt))) (join t₁₂ t₃) λ t₃ →
    split t₃ 2

  -- run Ctrl-C Ctrl-N here
  compute = {! example  !}
