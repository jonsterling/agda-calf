{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence where

open import Calf
open import Calf.Types.Unit
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Bool
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.List

open import Level using (0ℓ)
open import Relation.Binary
open import Data.Nat as Nat using (_<_)
import Data.Nat.Properties as Nat
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Function using (case_of_)


open import Examples.Sequence.MSequence
open import Examples.Sequence.ListMSequence
open import Examples.Sequence.RedBlackMSequence


module Ex/FromList where
  open MSequence RedBlackMSequence

  fromList : cmp (Π (list nat) λ _ → F (seq nat))
  fromList [] = empty
  fromList (x ∷ l) =
    bind (F (seq nat)) empty λ s₁ →
    bind (F (seq nat)) (fromList l) λ s₂ →
    join s₁ x s₂

  example : cmp (F (seq nat))
  example = fromList (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])


module BinarySearchTree
  (MSeq : MSequence)
  (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ)
  where

  open StrictTotalOrder Key

  𝕂 : tp pos
  𝕂 = U (meta (StrictTotalOrder.Carrier Key))

  open MSequence MSeq public

  singleton : cmp (Π 𝕂 λ _ → F (seq 𝕂))
  singleton a =
    bind (F (seq 𝕂)) empty λ t →
    join t a t

  Split : tp neg
  Split = F (prod⁺ (seq 𝕂) (prod⁺ (maybe 𝕂) (seq 𝕂)))

  split : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → Split)
  split t a =
    rec
      {X = F (prod⁺ (seq 𝕂) (prod⁺ (maybe 𝕂) (seq 𝕂)))}
      (bind Split empty λ t →
        ret (t , nothing , t))
      (λ t₁ ih₁ a' t₂ ih₂ →
        case compare a a' of λ
          { (tri< a<a' ¬a≡a' ¬a>a') →
              bind Split ih₁ λ ( t₁₁ , a? , t₁₂ ) →
              bind Split (join t₁₂ a' t₂) λ t →
              ret (t₁₁ , a? , t)
          ; (tri≈ ¬a<a' a≡a' ¬a>a') → ret (t₁ , just a' , t₂)
          ; (tri> ¬a<a' ¬a≡a' a>a') →
              bind Split ih₂ λ ( t₂₁ , a? , t₂₂ ) →
              bind Split (join t₁ a' t₂₁) λ t →
              ret (t , a? , t₂₂)
          })
      t

  find : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → F (maybe 𝕂))
  find t a = bind (F (maybe 𝕂)) (split t a) λ { (_ , a? , _) → ret a? }

  insert : cmp (Π (seq 𝕂) λ _ → Π 𝕂 λ _ → F (seq 𝕂))
  insert t a = bind (F (seq 𝕂)) (split t a) λ { (t₁ , _ , t₂) → join t₁ a t₂ }


module Ex/NatSet where
  open BinarySearchTree RedBlackMSequence Nat.<-strictTotalOrder

  example : cmp Split
  example =
    bind Split (singleton 1) λ t₁ →
    bind Split (insert t₁ 2) λ t₁ →
    bind Split (singleton 4) λ t₂ →
    bind Split (join t₁ 3 t₂) λ t →
    split t 2


module Ex/NatStringDict where
  strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
  strictTotalOrder =
    record
      { Carrier = ℕ × String
      ; _≈_ = λ (n₁ , _) (n₂ , _) → n₁ ≡ n₂
      ; _<_ = λ (n₁ , _) (n₂ , _) → n₁ < n₂
      ; isStrictTotalOrder =
          record
            { isEquivalence =
                record
                  { refl = Eq.refl
                  ; sym = Eq.sym
                  ; trans = Eq.trans
                  }
            ; trans = Nat.<-trans
            ; compare = λ (n₁ , _) (n₂ , _) → Nat.<-cmp n₁ n₂
            }
      }

  open BinarySearchTree RedBlackMSequence strictTotalOrder

  example : cmp Split
  example =
    bind Split (singleton (1 , "red")) λ t₁ →
    bind Split (insert t₁ (2 , "orange")) λ t₁ →
    bind Split (singleton (4 , "green")) λ t₂ →
    bind Split (join t₁ (3 , "yellow") t₂) λ t →
    split t (2 , "")
