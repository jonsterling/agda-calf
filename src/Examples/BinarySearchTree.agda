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
open import Calf.Types.Bool
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.List
open import Data.String using (String)
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_)
open import Data.Bool as Bool using (not; _∧_)
import Data.Nat.Properties as Nat

open import Function

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
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

  Split : tp neg
  Split = F (prod⁺ bst (prod⁺ (maybe 𝕂) bst))

  split : cmp (Π bst λ _ → Π 𝕂 λ _ → Split)
  split t k =
    rec
      {X = F (prod⁺ bst (prod⁺ (maybe 𝕂) bst))}
      (bind Split empty λ t →
        ret (t , nothing , t))
      (λ t₁ ih₁ k' t₂ ih₂ →
        case compare k k' of λ
          { (tri< k<k' ¬k≡k' ¬k>k') →
              bind Split ih₁ λ ( t₁₁ , k? , t₁₂ ) →
              bind Split (node t₁₂ k' t₂) λ t →
              ret (t₁₁ , k? , t)
          ; (tri≈ ¬k<k' k≡k' ¬k>k') → ret (t₁ , just k' , t₂)
          ; (tri> ¬k<k' ¬k≡k' k>k') →
              bind Split ih₂ λ ( t₂₁ , k? , t₂₂ ) →
              bind Split (node t₁ k' t₂₁) λ t →
              ret (t , k? , t₂₂)
          })
      t

  find : cmp (Π bst λ _ → Π 𝕂 λ _ → F (maybe 𝕂))
  find t k = bind (F (maybe 𝕂)) (split t k) λ { (_ , k? , _) → ret k? }

  insert : cmp (Π bst λ _ → Π 𝕂 λ _ → F bst)
  insert t k = bind (F bst) (split t k) λ { (t₁ , _ , t₂) → node t₁ k t₂ }


ListBST : (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) → ParametricBST Key
ListBST Key =
  record
    { bst = list 𝕂
    ; leaf = ret []
    ; node = λ l₁ k l₂ → ret (l₁ ++ [ k ] ++ l₂)
    ; rec = λ {X} → rec {X}
    }
  where
    𝕂 : tp pos
    𝕂 = U (meta (StrictTotalOrder.Carrier Key))

    rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (list 𝕂) λ _ → Π (U X) λ _ → Π 𝕂 λ _ → Π (list 𝕂) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (list 𝕂) λ _ → X
        )
    rec {X} z f []      = z
    rec {X} z f (x ∷ l) = step X (1 , 1) (f [] z x l (rec {X} z f l))


RedBlackBST' : (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) → ParametricBST Key
RedBlackBST' Key =
  record
    { bst = rbt
    ; leaf = ret leaf
    ; node = joinMid
    ; rec = λ {X} → rec {X}
    }
  where
    𝕂 : tp pos
    𝕂 = U (meta (StrictTotalOrder.Carrier Key))

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
                            --  bind (F rbt) (joinRight r' k t₂) (λ r'' →
                             bind {A = rbt} (F rbt) {!   !} (λ r'' →  -- placate termination checking
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


RedBlackBST : (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) → ParametricBST Key
RedBlackBST Key =
  record
    { bst = rbt
    ; leaf = ret ⟪ leaf ⟫
    ; node = joinMid
    ; rec = λ {X} → rec {X}
    }
  where
    𝕂 : tp pos
    𝕂 = U (meta (StrictTotalOrder.Carrier Key))

    data Color : Set where
      red : Color
      black : Color
    color : tp pos
    color = U (meta Color)

    -- Indexed Red Black Tree
    data IRBT : val color → val nat → Set where
      leaf  : IRBT black zero
      red   : {n : val nat}
        (t₁ : IRBT black n) (k : val 𝕂) (t₂ : IRBT black n)
        → IRBT red n
      black : {n : val nat} {y₁ y₂ : val color}
        (t₁ : IRBT y₁ n) (k : val 𝕂) (t₂ : IRBT y₂ n)
        → IRBT black (suc n)
    irbt : val color → val nat → tp pos
    irbt y n = U (meta (IRBT y n))

    record RBT : Set where
      pattern
      constructor ⟪_⟫
      field
        {y} : val color
        {n} : val nat
        t : val (irbt y n)
    rbt : tp pos
    rbt = U (meta RBT)

    -- Just Join for Parallel Ordered Sets (Blelloch, Ferizovic, and Sun)
    -- https://diderot.one/courses/121/books/492/chapter/6843

    i-joinRight :
      cmp
        ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
          Π 𝕂 λ _ →
          Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
          Π (U (meta (n₁ ≥ n₂))) λ _ →
          F (irbt y₁ n₁)  -- TODO: is this correct?
        )
    i-joinRight y₁ n₁ t₁ k y₂ n₂ t₂ n₁≥n₂ with n₁ Nat.≟ n₂
    ... | yes refl = ret {!  red !}
    i-joinRight .black .zero leaf k y₂ .zero t₂ Nat.z≤n | no n₁≢n₂ = contradiction refl n₁≢n₂
    i-joinRight .red n₁ (red t₁₁ k₁ t₁₂) k y₂ n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
      bind (F {!   !}) (i-joinRight _ _ t₁₂ k _ _ t₂ {!     !}) λ t₂' →
      ret (red t₁₁ k₁ t₂')
    i-joinRight .black .(suc _) (black t₁₁ k₁ t₁₂) k y₂ n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
      {!   !}

    i-joinMid :
      cmp
        ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
          Π 𝕂 λ _ →
          Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
          F rbt
        )
    i-joinMid y₁ n₁ t₁ k y₂ n₂ t₂ with Nat.<-cmp n₁ n₂
    i-joinMid red n₁ t₁ k y₂ n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    i-joinMid black n₁ t₁ k red n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    i-joinMid black n₁ t₁ k black n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (red t₁ k t₂) ⟫
    ... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ = {!   !}
    ... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
      bind (F rbt) (i-joinRight _ _ t₁ k _ _ t₂ (Nat.<⇒≤ n₁>n₂)) λ t →
      {!   !}

    joinMid : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
    joinMid ⟪ t₁ ⟫ k ⟪ t₂ ⟫ = i-joinMid _ _ t₁ k _ _ t₂

    i-rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π
            ( U
              ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ → Π (U X) λ _ →
                Π 𝕂 λ _ →
                Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ → Π (U X) λ _ →
                X
              )
            ) λ _ →
          Π color λ y → Π nat λ n → Π (irbt y n) λ _ →
          X
        )
    i-rec {X} z f .black .zero    leaf            = z
    i-rec {X} z f .red   n        (red   t₁ k t₂) =
      f
        _ _ t₁ (i-rec {X} z f _ _ t₁)
        k
        _ _ t₂ (i-rec {X} z f _ _ t₂)
    i-rec {X} z f .black .(suc _) (black t₁ k t₂) =
      f
        _ _ t₁ (i-rec {X} z f _ _ t₁)
        k
        _ _ t₂ (i-rec {X} z f _ _ t₂)

    rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π rbt λ _ → Π (U X) λ _ → Π 𝕂 λ _ → Π rbt λ _ → Π (U X) λ _ → X)) λ _ →
          Π rbt λ _ → X
        )
    rec {X} z f ⟪ t ⟫ =
      i-rec {X}
        z
        (λ _ _ t₁ ih₁ k _ _ t₂ ih₂ → f ⟪ t₁ ⟫ ih₁ k ⟪ t₂ ⟫ ih₂)
        _ _ t


module Ex/NatSet-List where
  open ParametricBST (ListBST Nat.<-strictTotalOrder)

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
