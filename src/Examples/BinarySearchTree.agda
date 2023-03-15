{-# OPTIONS --prop --rewriting #-}

module Examples.BinarySearchTree where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Level using (0ℓ)

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Unit
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.Bool
open import Data.String using (String)
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_)
open import Data.Bool as Bool using (not; _∧_)
import Data.Nat.Properties as Nat

open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)

variable
  A B C : tp pos
  X Y Z : tp neg
  P Q : val A → tp neg


record ParametricBST (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) : Set₁ where
  open StrictTotalOrder Key

  𝕂 : tp pos
  𝕂 = U (meta (StrictTotalOrder.Carrier Key))

  field
    bst : tp pos

    leaf : cmp (F bst)
    node : cmp (Π bst λ t₁ → Π 𝕂 λ k → Π bst λ t₂ → F bst)

    rec :
      cmp
        ( Π (U X) λ _ →
          Π (U (Π bst λ _ → Π (U X) λ _ → Π 𝕂 λ _ → Π bst λ _ → Π (U X) λ _ → X)) λ _ →
          Π bst λ _ → X
        )

  empty : cmp (F bst)
  empty = leaf

  singleton : cmp (Π 𝕂 λ _ → F bst)
  singleton k =
    bind (F bst) empty λ t →
    node t k t

  record %Split : Set where
    constructor [_,_,_]
    field
      left : cmp (F bst)
      value : cmp (F (maybe 𝕂))
      right : cmp (F bst)
  open %Split
  -- (left : F bst) × (value : F (maybe 𝕂)) × (right : F bst)
  Split : tp neg
  Split = meta %Split

  split : cmp (Π bst λ _ → Π 𝕂 λ _ → Split)
  split t k =
    rec
      {X = Split}
      [ empty , ret nothing , empty ]
      (λ t₁ ih₁ k' t₂ ih₂ →
        case compare k k' of λ
          { (tri< k<k' ¬k≡k' ¬k>k') →
              [ left ih₁ , value ih₁ , bind (F bst) (right ih₁) (λ t → node t k' t₂) ]
          ; (tri≈ ¬k<k' k≡k' ¬k>k') → [ ret t₁ , ret (just k') , ret t₂ ]
          ; (tri> ¬k<k' ¬k≡k' k>k') →
              [ bind (F bst) (left ih₂) (λ t → node t₁ k' t) , value ih₂ , right ih₂ ]
          })
      t

  find : cmp (Π bst λ _ → Π 𝕂 λ _ → F (maybe 𝕂))
  find t k = value (split t k)

  insert : cmp (Π bst λ _ → Π 𝕂 λ _ → F bst)
  insert t k =
    bind (F bst) (left (split t k) & right (split t k)) λ (t₁ , t₂) →
    node t₁ k t₂


RedBlackBST : (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) → ParametricBST Key
RedBlackBST Key =
  record
    { bst = rbt
    ; leaf = ret leaf
    ; node = joinMid
    ; rec = λ {X} → rec {X}
    }
  where
    open StrictTotalOrder Key

    𝕂 : tp pos
    𝕂 = U (meta Carrier)

    data RBT : Set where
      leaf  : RBT
      red   : (t₁ : RBT) (k : val 𝕂) (t₂ : RBT) → RBT
      black : (t₁ : RBT) (k : val 𝕂) (t₂ : RBT) → RBT
    rbt : tp pos
    rbt = U (meta RBT)

    isBlack : cmp (Π rbt λ _ → F bool)
    isBlack leaf = ret true
    isBlack (red _ _ _) = ret false
    isBlack (black _ _ _) = ret true

    isRed : cmp (Π rbt λ _ → F bool)
    isRed t = bind (F bool) (isBlack t) (λ b → ret (not b))

    rank : cmp (Π rbt λ _ → F nat)
    rank t = bind (F nat) (h t) (λ hₜ →
             bind (F nat) (isBlack t) (λ b →
             if b
             then (ret (2 * hₜ - 2))
             else (ret (2 * hₜ - 1))))
      where
        -- black height
        -- invariant is not explicitly maintained
        -- invariant used: every path from root to leaf has the same black height
        h : cmp (Π rbt λ _ → F nat)
        h leaf = ret 1
        h (red t k _) = h t
        h (black t k _) = bind (F nat) (h t) (λ hₜ → ret (hₜ + 1))

        _-_ : ℕ → ℕ → ℕ
        n     - zero  = n
        zero  - suc m = zero
        suc n - suc m = n - m

    -- halfFloor : ℕ → ℕ
    -- halfFloor zero = zero
    -- halfFloor (suc zero) = zero
    -- halfFloor (suc (suc n)) = suc (halfFloor n)

    half : cmp (Π nat λ _ → F nat)
    half n = ret (⌊ n /2⌋ )

    rightChild : cmp (Π rbt λ _ → F rbt)
    rightChild leaf = ret leaf
    rightChild (red _ _ t₂) = ret t₂
    rightChild (black _ _ t₂) = ret t₂

    leftChild : cmp (Π rbt λ _ → F rbt)
    leftChild leaf = ret leaf
    leftChild (red t₁ _ _) = ret t₁
    leftChild (black t₁ _ _) = ret t₁

    rotateLeft : cmp (Π rbt λ _ → F rbt)
    rotateLeft t = {!   !}

    -- {-# NON_TERMINATING #-}
    joinRight : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
    joinRight t₁ k t₂ = bind (F rbt) (rank t₁) (λ r₁ →
                        bind (F rbt) (rank t₂) (λ r₂ →
                        bind (F rbt) (half r₂) (λ r₃ →
                        if (r₁ ≡ᵇ (2 * r₃))
                        then ret (red t₁ k t₂)
                        else bind (F rbt) (expose t₁) (λ (l' , k' , r') →
                             bind (F rbt) (isRed t₁) (λ b →
                             bind (F rbt) (joinRight r' k t₂) (λ r'' →
                             if b
                             then (bind (F rbt) (redT' l' k' r'') (λ t' →
                                   bind (F rbt) (rightChild t') (λ rt' →
                                   bind (F rbt) (rightChild rt') λ rrt' →
                                   bind (F rbt) (isRed rt') (λ b₁ →
                                   bind (F rbt) (isRed rrt') (λ b₂ →
                                   if (not b ∧ b₁ ∧ b₂)
                                   then bind (F rbt) (expose rrt') (λ (t₁' , k'' , t₂') →
                                        bind (F rbt) (blackT' t₁' k'' t₂') (λ rrt'' →
                                        bind (F rbt) (switchRightChild r'' rrt'') (λ t →
                                        bind (F rbt) (rotateLeft t) (λ t'' → ret t''))))
                                   else ret t')))))
                             else (bind (F rbt) (blackT' l' k' r'') (λ t' →
                                   bind (F rbt) (rightChild t') (λ rt' →
                                   bind (F rbt) (rightChild rt') λ rrt' →
                                   bind (F rbt) (isRed rt') (λ b₁ →
                                   bind (F rbt) (isRed rrt') (λ b₂ →
                                   if (not b ∧ b₁ ∧ b₂)
                                   then bind (F rbt) (expose rrt') (λ (t₁' , k'' , t₂') →
                                        bind (F rbt) (blackT' t₁' k'' t₂') (λ rrt'' →
                                        bind (F rbt) (switchRightChild r'' rrt'') (λ t →
                                        bind (F rbt) (rotateLeft t) (λ t'' → ret t''))))
                                   else ret t')))))))))))
      where
        expose : cmp (Π rbt λ _ → F (prod⁺ rbt (prod⁺ 𝕂 rbt)))
        expose leaf = {!   !} -- TODO: maintian invariant
        expose (red t₁ k t₂) = ret (t₁ , k , t₂ )
        expose (black t₁ k t₂) = ret (t₁ , k , t₂ )

        switchRightChild : cmp (Π rbt λ _ → Π rbt λ _ → F rbt)
        switchRightChild leaf t₂ = {!   !}
        switchRightChild (red t₁ k t₃) t₂ = ret (red t₁ k t₂)
        switchRightChild (black t₁ k t₃) t₂ = ret (black t₁ k t₂)

        redT' : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
        redT' t₁ k t₂ = ret (red t₁ k t₂)

        blackT' : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
        blackT' t₁ k t₂ = ret (black t₁ k t₂)

    joinLeft : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
    joinLeft t₁ k t₂ = {!   !}

    -- Just Join for Parallel Ordered Sets (Blelloch, Ferizovic, and Sun)
    -- https://diderot.one/courses/121/books/492/chapter/6843
    joinMid : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
    joinMid t₁ k t₂ = bind (F rbt) (rank t₁) (λ rₗ →
                      bind (F rbt) (rank t₂) (λ rᵣ →
                      bind (F rbt) (half rₗ) (λ r₁ →
                      bind (F rbt) (half rᵣ) (λ r₂ →
                      if not (r₁ ≤ᵇ r₂)
                      then bind (F rbt) (joinRight t₁ k t₂) (λ t' →
                           bind (F rbt) (key t') (λ k' →
                           bind (F rbt) (isRed t') (λ b₁ →
                           bind (F rbt) (rightChild t') (λ rt' →
                           bind (F rbt) (leftChild t') (λ lt' →
                           bind (F rbt) (isRed rt') λ b₂ →
                           if b₁ ∧ b₂
                           then ret (black lt' k' rt')
                           else ret t')))))
                      else (if (r₁ <ᵇ r₂)
                            then (bind (F rbt) (joinLeft t₁ k t₂) λ t' →
                                  bind (F rbt) (key t') (λ k' →
                                  bind (F rbt) (isRed t') (λ b₁ →
                                  bind (F rbt) (rightChild t') (λ rt' →
                                  bind (F rbt) (leftChild t') (λ lt' →
                                  bind (F rbt) (isRed lt') λ b₂ →
                                  if b₁ ∧ b₂
                                  then ret (black lt' k' rt')
                                  else ret t')))))
                            else bind (F rbt) (isBlack t₁) (λ b₁ →
                                 bind (F rbt) (isBlack t₂) (λ b₂ →
                                 if b₁ ∧ b₂
                                 then ret (red t₁ k t₂)
                                 else ret (black t₁ k t₂))))))))
      where
        key : cmp (Π rbt λ _ → F 𝕂)
        key leaf = ret {!   !} -- TODO: maintian invariant
        key (red _ k _) = ret k
        key (black _ k _) = ret k


    rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π rbt λ _ → Π (U X) λ _ → Π 𝕂 λ _ → Π rbt λ _ → Π (U X) λ _ → X)) λ _ →
          Π rbt λ _ → X
        )
    rec {X} z f leaf = z
    rec {X} z f (red   t₁ k t₂) = f t₁ (rec {X} z f t₁) k t₂ (rec {X} z f t₂)
    rec {X} z f (black t₁ k t₂) = f t₁ (rec {X} z f t₁) k t₂ (rec {X} z f t₂)


module Ex/NatSet where
  open ParametricBST (RedBlackBST Nat.<-strictTotalOrder)

  example : cmp Split
  example =
    bind Split (singleton 1) λ t₁ →
    bind Split (insert t₁ 2) λ t₁ →
    bind Split (singleton 4) λ t₂ →
    bind Split (node t₁ 3 t₂) λ t →
    split t 2

  -- run Ctrl-C Ctrl-N here
  compute : cmp Split
  compute = {! example  !}

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

  open ParametricBST (RedBlackBST strictTotalOrder)

  example : cmp Split
  example =
    bind Split (singleton (1 , "red")) λ t₁ →
    bind Split (insert t₁ (2 , "orange")) λ t₁ →
    bind Split (singleton (4 , "green")) λ t₂ →
    bind Split (node t₁ (3 , "yellow") t₂) λ t →
    split t (2 , "")

  -- run Ctrl-C Ctrl-N here
  compute : cmp Split
  compute = {! example  !}
