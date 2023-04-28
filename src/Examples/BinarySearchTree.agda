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
    ; node =
        λ l₁ k l₂ →
          let n = length l₁ + 1 + length l₂ in
          step (F (list 𝕂)) (n , n) (ret (l₁ ++ [ k ] ++ l₂))
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

    -- data HRBT : val nat → Set where
    --   hred : {m : val nat} → IRBT red m → HRBT m
    --   hblack : {m : val nat} → IRBT black (suc m) → HRBT (suc m)
    -- hrbt : val nat → tp pos
    -- hrbt n = U (meta (HRBT n))

    -- height : val color → val nat → val nat
    -- height red n = n
    -- height black n = suc n

    -- data AlmostRBT : val nat → Set where
    --   at :   {n : val nat} { c1 c2 : val color}
    --           → (c : val color)
    --           → IRBT c1 n → val 𝕂 → IRBT c2 n
    --           → AlmostRBT (height c n)
    -- arbt : val nat → tp pos
    -- arbt n = U (meta (AlmostRBT n))

    data HiddenRBT : val nat → Set where
      redhd : {n : val nat} → IRBT red n → HiddenRBT n
      blackhd : {n : val nat} → IRBT black n → HiddenRBT n
    hrbt : val nat → tp pos
    hrbt n = U (meta (HiddenRBT n))

    data AlmostRightRBT : val nat → Set where
      redat :   {n : val nat} { c1 : val color}
              → IRBT black n → val 𝕂 → IRBT c1 n
              → AlmostRightRBT n
      blackat : {n : val nat} { c1 c2 : val color}
              → IRBT c1 n → val 𝕂 → IRBT c2 n
              → AlmostRightRBT (suc n)
    arrbt : val nat → tp pos
    arrbt n = U (meta (AlmostRightRBT n))

    joinEqual : cmp (
                       Π nat λ n₁ → Π (irbt black (suc n₁)) λ _ →
                       Π 𝕂 λ _ →
                       Π color λ y₂ → Π (irbt y₂ n₁) λ _ →
                       F (hrbt (suc n₁))
                    )
    joinEqual .zero (black t₁ k₁ leaf) k .black leaf = ret (blackhd (black t₁ k₁ (red leaf k leaf)))
    joinEqual .zero (black t₁ k₁ leaf) k .red (red t₂ k₂ t₃) = ret (redhd (red (black t₁ k₁ leaf) k (black t₂ k₂ t₃))) --rotate
    joinEqual .zero (black t₁ k₁ (red t₃ k₂ t₄)) k .black leaf = ret (redhd (red (black t₁ k₁ t₃) k₂ (black t₄ k leaf))) --rotate
    joinEqual n₁ (black t₁ k₁ (red t₃ k₂ t₄)) k .red (red t₂ k₃ t₅) = ret (redhd (red (black t₁ k₁ t₃) k₂ (black t₄ k (red t₂ k₃ t₅)))) -- 3R god
    joinEqual .(suc _) (black t₁ k₁ (red t₃ k₂ t₄)) k .black (black t₂ k₃ t₅) = ret (redhd (red (black t₁ k₁ t₃) k₂ (black t₄ k (black t₂ k₃ t₅)))) --rotate
    joinEqual .(suc _) (black t₁ k₁ (black t₃ k₂ t₄)) k .red (red t₂ k₃ t₅) = ret (redhd (red (black t₁ k₁ (black t₃ k₂ t₄)) k (black t₂ k₃ t₅))) --rotate
    joinEqual .(suc _) (black t₁ k₁ (black t₃ k₂ t₄)) k .black (black t₂ k₃ t₅) = ret (blackhd (black t₁ k₁ (red (black t₃ k₂ t₄) k (black t₂ k₃ t₅))))

    mutual
      jj-joinRight : cmp (
                       Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
                       Π 𝕂 λ _ →
                       Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
                       Π (U (meta (n₁ > n₂))) λ _ →
                       F (arrbt n₁)
                      )
      jj-joinRight .red n₁ (red t₁ k₁ t₃) k y₂ n₂ t₂ p =
        bind (F (arrbt n₁)) (jj-joinRight' _ t₃ k _ _ t₂ p) (λ { (redhd t₄) → ret (redat t₁ k₁ t₄)
                                                               ; (blackhd t₄) → ret (redat t₁ k₁ t₄) })
      jj-joinRight .black (suc n₁) (black t₁ k₁ t₃) k y₂ n₂ t₂ p with n₁ Nat.≟ n₂
      ... | yes refl =
        bind (F (arrbt (suc n₁))) (joinEqual n₁ (black t₁ k₁ t₃) k _ t₂) (λ { (redhd (red t₄ k₂ t₅)) → ret (redat t₄ k₂ t₅) --weaken
                                                                            ; (blackhd (black t₄ k₂ t₅)) → ret (blackat t₄ k₂ t₅) })
      ... | no p₁ =
        bind (F (arrbt (suc n₁))) (jj-joinRight _ _ t₃ k _ _ t₂ {!   !}) λ { (redat t₄ k₂ leaf) → ret (blackat t₁ k₁ (red t₄ k₂ leaf))
                                                                            ; (redat t₄ k₂ (red t₅ k₃ t₆)) → ret (redat (black t₁ k₁ t₄) k₂ (black t₅ k₃ t₆)) --rotate
                                                                            ; (redat t₄ k₂ (black t₅ k₃ t₆)) → ret (blackat t₁ k₁ (black t₅ k₃ t₆))
                                                                            ; (blackat t₄ k₂ t₅) → ret (blackat t₁ k₁ (black t₄ k₂ t₅)) }

      jj-joinRight' : cmp (
                       Π nat λ n₁ → Π (irbt black n₁) λ _ →
                       Π 𝕂 λ _ →
                       Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
                       Π (U (meta (n₁ > n₂))) λ _ →
                       F (hrbt n₁)
                      )
      jj-joinRight' (suc n₁) (black t₁ k₁ t₃) k y₂ n₂ t₂ p with n₁ Nat.≟ n₂
      ... | yes refl =
        bind (F (hrbt (suc n₁))) (joinEqual n₁ (black t₁ k₁ t₃) k _ t₂) ret
      ... | no p₁ =
        bind (F (hrbt (suc n₁))) (jj-joinRight _ _ t₃ k _ _ t₂ {!   !}) λ { (redat t₄ k₂ (red t₅ k₃ t₆)) → ret (redhd (red (black t₁ k₁ t₄) k₂ (black t₅ k₃ t₆))) -- rotate
                                                                           ; (redat t₄ k₂ leaf) → ret (blackhd (black t₁ k₁ (red t₄ k₂ leaf)))
                                                                           ; (redat t₄ k₂ (black t₅ k₃ t₆)) → ret (blackhd (black t₁ k₁ (red t₄ k₂ (black t₅ k₃ t₆))))
                                                                           ; (blackat t₄ k₂ t₅) → ret (blackhd (black t₁ k₁ (black t₄ k₂ t₅))) }

    -- data InsRBT : Set where
    --   root : {n : val nat} → IRBT black n → InsRBT
    -- insrbt : tp pos
    -- insrbt = U (meta InsRBT)

    record RBT : Set where
      pattern
      constructor ⟪_⟫
      field
        {y} : val color
        {n} : val nat
        t : val (irbt y n)
    rbt : tp pos
    rbt = U (meta RBT)

    -- data JRBT : Set where
    --   root : {n : val nat} { c : val color } → IRBT c n → JRBT
    -- jrbt : tp pos
    -- jrbt = U (meta JRBT)

    -- j-rotateLeft : cmp (
    --                 Π color λ y → Π 𝕂 λ _ →
    --                 Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --                 Π nat λ n₂ → Π (arbt n₂) λ { (at red t₂ k₁ t₃) → F (arbt n₂) ; (at black t₂ k₁ t₃) → F (arbt n₂) }
    --                 -- F (arbt n₁)
    --               )
    -- j-rotateLeft y k y₁ n₁ t₁ .(height red _) (at red t₂ k₁ t₃) =
    --   ret (at red {!   !} k₁ {!  t₃ !})
    -- j-rotateLeft y k y₁ n₁ t₁ .(height black _) (at black t₂ k₁ t₃) =
    --   ret (at {!  black !} {!   !} {!   !} {!   !})

    -- ≤-≢ : {n₁ n₂ : ℕ} → n₂ ≤ (suc n₁) → ¬ (suc n₁) ≡ n₂ → n₂ ≤ n₁
    -- -- ≤-≢ h₁ h₂ = ?
    -- ≤-≢ : cmp (
    --       Π nat λ n₁ → Π nat λ n₂ →
    --       Π (U (meta ((suc n₁) ≥ n₂))) λ _ → Π (U (meta (¬ (suc n₁) ≡ n₂))) λ _ →
    --       meta (n₁ ≥ n₂)
    --     )
    -- ≤-≢ n₁ .zero Nat.z≤n h₂ = Nat.z≤n
    -- ≤-≢ n₁ (suc n₂) (Nat.s≤s h₁) h₂ with n₁ Nat.≟ (suc n₂)
    -- ... | yes refl = Nat.s≤s {!   !}
    -- ... | no n₁≢n₂ = {!   !}

    -- j-joinRight : cmp (
    --                  Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --                  Π 𝕂 λ _ →
    --                  Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --                  Π (U (meta (n₁ ≥ n₂))) λ _ →
    --                  F (arrbt n₁)
    --                 )
    -- j-joinRight y₁ n₁ t₁ k y n₂ t₂ n₁≥n₂ with n₁ Nat.≟ n₂
    -- j-joinRight .black .zero leaf k y .zero t₂ n₁≥n₂ | yes refl = ret (redat leaf k leaf)
    -- j-joinRight .red n₁ (red t₁ k₁ t₃) k y .n₁ t₂ n₁≥n₂ | yes refl =
    --   bind (F (arrbt n₁)) (j-joinRight _ _ t₃ k _ _ t₂ n₁≥n₂) λ { (redat t₄ k₂ t₅) → {!   !}
    --                                                             ; (blackat t₄ k₂ t₅) → ret (redat t₁ k (black t₄ k₂ t₅)) }
    -- j-joinRight .black .(suc _) (black t₁ k₁ t₃) k y .(suc _) t₂ n₁≥n₂ | yes refl = ret (redat (black t₁ k₁ t₃) k t₂)
    -- j-joinRight .black .zero leaf k y .zero t₂ Nat.z≤n | no n₁≢n₂ = contradiction refl n₁≢n₂
    -- j-joinRight .red n₁ (red t₁ k₁ t₃) k y n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
    --   bind (F (arrbt n₁)) ((j-joinRight _ _ t₃ k _ _ t₂ n₁≥n₂)) λ { (redat t₄ k₂ t₅) → ret (redat {!   !} k {!   !})
    --                                                               ; (blackat t₄ k₂ t₅) → ret (redat t₁ k (black t₄ k₂ t₅)) }
    -- j-joinRight .black (suc n₁) (black t₁ k₁ t₃) k y n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
    --   bind (F (arrbt (suc n₁))) (j-joinRight _ _ t₃ k _ _ t₂ {!   !}) λ { (redat t₄ k₂ leaf) → ret (blackat t₁ k (red t₄ k₂ leaf))
    --                                                                      ; (redat t₄ k₂ (red t₅ k₃ t₆)) → ret (redat (black t₁ k t₄) k₂ (black t₅ k₃ t₆)) --rotate
    --                                                                      ; (redat t₄ k₂ (black t₅ k₃ t₆)) → ret (blackat t₁ k (red t₄ k₂ (black t₅ k₃ t₆)))
    --                                                                      ; (blackat t₄ k₂ t₅) → ret (blackat t₁ k (black t₄ k₂ t₅)) }

    -- j-joinRight' : cmp (
    --                  Π nat λ n₁ → Π (irbt black n₁) λ _ →
    --                  Π 𝕂 λ _ →
    --                  Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --                  Π (U (meta (n₁ ≥ n₂))) λ _ →
    --                  F (Σ (y) (irbt y n₁))
    --                 )
    -- j-joinRight' n₁ t₁ k y₂ n₂ t₃ n₁≥n₂ with with n₁ Nat.≟ n₂
    -- ... | yes refl = ?
    -- ... | no h = ?

    -- joinRightBlack : cmp (
    --                  Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --                  Π 𝕂 λ _ →
    --                  Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --                  Π (U (meta (n₁ ≥ n₂))) λ _ →
    --                  F (arbt n₁)
    --                 )
    -- joinRightBlack y₁ n₁ t₁ k y n₂ t₂ n₁≥n₂ with n₁ Nat.≟ n₂
    -- ... | yes refl = ret (at red t₁ k t₂)
    -- joinRightBlack black .zero leaf k y .zero t₂ Nat.z≤n | no n₁≢n₂ = contradiction refl n₁≢n₂
    -- joinRightBlack red n₁ (red t₁ k₁ t₃) k y n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
    --   bind (F (arbt n₁)) (joinRightBlack _ _ t₃ k _ _ t₂ n₁≥n₂) (λ { (at red t₄ k₂ t₅) → {!   !}
    --                                                                ; (at black t₄ k₂ t₅) → {!   !} })
    -- joinRightBlack black (suc n₁) (black t₁ k₁ t₃) k y n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
    --   bind (F (arbt (suc n₁))) (joinRightBlack _ _ t₃ k _ _ t₂ {!   !}) λ { (at red t₄ k₂ leaf) → {!   !}
    --                                                                         ; (at red t₄ k₂ (red t₅ k₃ t₆)) → ret (at red (black t₁ k t₄) k₂ (black t₅ k₃ t₆)) --rotate
    --                                                                         ; (at red t₄ k₂ (black t₅ k₃ t₆)) → {!   !}
    --                                                                         ; (at black t₄ k₂ t₅) → ret (at black t₁ k (black t₄ k₂ t₅))
    --                                                                       --  }
    j-joinMid :
      cmp
        ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
          Π 𝕂 λ _ →
          Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
          F (rbt)
        )
    j-joinMid y₁ n₁ t₁ k y₂ n₂ t₂ with Nat.<-cmp n₁ n₂
    j-joinMid red n₁ t₁ k y₂ n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    j-joinMid black n₁ t₁ k red n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    j-joinMid black n₁ t₁ k black n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (red t₁ k t₂) ⟫
    ... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ =
      {!   !}
    ... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
      bind (F rbt) (jj-joinRight _ _ t₁ k _ _ t₂ (n₁>n₂)) λ { (redat t₃ k₁ (red t₄ k₂ t₅)) → ret ⟪ black t₃ k₁ (red t₄ k₂ t₅) ⟫
                                                            ; (redat t₃ k₁ (black t₄ k₂ t₅)) → ret ⟪ red t₃ k₁ (black t₄ k₂ t₅) ⟫
                                                            ; (blackat t₃ k₁ t₄) → ret ⟪ black t₃ k₁ t₄ ⟫ }

    -- j-joinMid :
    --   cmp
    --     ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --       Π 𝕂 λ _ →
    --       Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --       F (rbt)
    --     )
    -- j-joinMid y₁ n₁ t₁ k y₂ n₂ t₂ with Nat.<-cmp n₁ n₂
    -- j-joinMid red n₁ t₁ k y₂ n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    -- j-joinMid black n₁ t₁ k red n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    -- j-joinMid black n₁ t₁ k black n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (red t₁ k t₂) ⟫
    -- ... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ =
    --   {!   !}
    -- ... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
    --   bind (F rbt) (joinRightBlack _ _ t₁ k _ _ t₂ (Nat.<⇒≤ n₁>n₂)) λ {
    --     (at red t₃ k₁ (red t₄ k₂ t₅)) → ret ⟪ black t₃ k₁ (red t₄ k₂ t₅) ⟫
    --   ; (at red (red t₃ k t₆) k₁ t₄) → ret ⟪ black (red t₃ k t₆) k₁ t₄ ⟫
    --   ; (at red (black t₃ k t₆) k₁ (black t₄ k₂ t₅)) → ret ⟪ red ((black t₃ k t₆)) k₁ ((black t₄ k₂ t₅)) ⟫
    --   ; (at black t₃ k₁ t₄) → ret ⟪ black t₃ k₁ t₄ ⟫ }

    -- rotateLeftB : cmp (
    --                Π color λ y → Π nat λ n → Π (arbt n) λ _ →
    --                Π 𝕂 λ _ →
    --                Π (irbt y n) λ _ →
    --                F (hrbt (suc n))
    --               )
    -- rotateLeftB y .(height red zero) (at red leaf k₁ leaf) k d = ret (hblack (black (red leaf k₁ leaf) k d))
    -- -- rotate
    -- rotateLeftB y .(height red zero) (at red leaf k₁ (red r₁ k₂ r₂)) k d = ret (hred (red (black leaf k₁ r₁) k₂ (black r₂ k d)))
    -- rotateLeftB y .(height black zero) (at black leaf k₁ r) k d = ret (hblack (black (black leaf k₁ r) k d))
    -- -- rotate
    -- rotateLeftB y .(height red _) (at red (red l₁ k₂ l₂) k₁ r) k d = ret (hred (red (black l₁ k₂ l₂) k₁ (black r k d)))
    -- rotateLeftB y .(height black _) (at black (red l₁ k₂ l₂) k₁ r) k d = ret (hblack (black (black (red l₁ k₂ l₂) k₁ r) k d))
    -- -- rotate
    -- rotateLeftB y .(height red (suc _)) (at red (black l₁ k₂ l₂) k₁ (red r₁ k₃ r₂)) k d = ret (hred (red (black (black l₁ k₂ l₂) k₁ r₁) k₃ (black r₂ k d)))
    -- rotateLeftB y .(height red (suc _)) (at red (black l₁ k₂ l₂) k₁ (black r₁ k₃ r₂)) k d = ret (hblack (black (red (black l₁ k₂ l₂) k₁ (black r₁ k₃ r₂)) k d))
    -- rotateLeftB y .(height black (suc _)) (at black (black l₁ k₂ l₂) k₁ r) k d = ret (hblack (black (black (black l₁ k₂ l₂) k₁ r) k d))

    -- rotateRightR : cmp (
    --                Π color λ y → Π nat λ n → Π (irbt y n) λ _ →
    --                Π 𝕂 λ _ →
    --                Π (hrbt n) λ _ →
    --                F (arbt n)
    --               )
    -- rotateRightR y n l k (hred r) = ret (at red l k r)
    -- rotateRightR y .(suc _) l k (hblack r) = ret (at red l k r)

    -- rotateLeftR : cmp (
    --                Π color λ y → Π nat λ n → Π (hrbt n) λ _ →
    --                Π 𝕂 λ _ →
    --                Π (irbt y n) λ _ →
    --                F (arbt n)
    --               )
    -- rotateLeftR y n (hred l) k r = ret (at red l k r)
    -- rotateLeftR y .(suc _) (hblack l) k r = ret (at red l k r)

    -- joinRight : cmp (
    --       Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --       Π 𝕂 λ _ →
    --       Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --       Π (U (meta (n₁ ≥ n₂))) λ _ →
    --       F (hrbt n₁)
    -- )

    -- rbt that removes invariants
    -- used in intermediate states
    -- data nRBT : Set where
    --   nleaf  : nRBT
    --   nred   : (t₁ : nRBT) (k : val 𝕂) (t₂ : nRBT) → nRBT
    --   nblack : (t₁ : nRBT) (k : val 𝕂) (t₂ : nRBT) → nRBT
    -- nrbt : tp pos
    -- nrbt = U (meta nRBT)

    -- irbt2nrbt : cmp (Π color λ y → Π nat λ n → Π (irbt y n) λ _ → F (nrbt))
    -- irbt2nrbt .black .zero leaf = ret nleaf
    -- irbt2nrbt .red n (red i k i₁) = bind (F nrbt) (irbt2nrbt black n i) (λ lhs →
    --                                 bind (F nrbt) (irbt2nrbt black n i₁) (λ rhs →
    --                                 ret (nred lhs k rhs)))
    -- irbt2nrbt .black .(suc _) (black i k i₁) = bind (F nrbt) (irbt2nrbt {! y₁  !} {! n  !} i) λ lhs →
    --                                            bind (F nrbt) (irbt2nrbt {! y₂ !} {! n  !} i₁) (λ rhs →
    --                                            ret (nblack lhs k rhs))

    -- rotateLeft : cmp (Π nrbt λ _ → F (nrbt))
    -- rotateLeft nleaf = ret nleaf
    -- rotateLeft (nred n k n₁) = {!   !}
    -- rotateLeft (nblack n k n₁) = {!   !}

    -- Just Join for Parallel Ordered Sets (Blelloch, Ferizovic, and Sun)
    -- https://diderot.one/courses/121/books/492/chapter/6843

    -- https://github.com/sweirich/dth/blob/master/depending-on-types/RBT.agda

    -- mutual
    --   joinRight :
    --     cmp
    --       ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --         Π 𝕂 λ _ →
    --         Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --         Π (U (meta (n₁ ≥ n₂))) λ _ →
    --         F (arbt n₁)
    --       )
    --   joinRight y₁ n₁ t₁ k y₂ n₂ t₂ n₁≥n₂ = {!   !} -- with n₁ Nat.≟ n₂
      -- ... | yes refl = ret (at red t₁ k t₂)
      -- joinRight .black .zero leaf k y₂ .zero t₂ Nat.z≤n | no n₁≢n₂ = contradiction refl n₁≢n₂
    -- joinRight .red n₁ (red t₁ k₁ t₃) k y₂ n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
      --      bind (F (arbt n₁)) (joinRight' _ t₃ k _ _ t₂ n₁≥n₂) λ { (hred t₃) → ret (at red t₁ k₁ t₃) ;
      --                                                              (hblack t₄) → ret (at red t₁ k t₄) }
      -- joinRight .black n₁ (black t₁ k₁ t₃) k y₂ n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
      --      bind (F (arbt n₁)) (joinRight _ _ t₃ k _ _ t₂ {!!}) (λ { (at red t₄ k₂ leaf) → ret (at black t₁ k₁ leaf) ; -- line 10 case
      --                                                                (at c t₄ k₂ (red t₅ k t₆)) → {!!} ;  -- line 9 case
      --                                                                (at red t₄ k₂ (black t₅ k t₆)) → ret (at black t₁ k₁ ( red {!!} {!!} {!!}))} ) -- line 10 case

    --   joinRight' : cmp (
    --         Π nat λ n₁ → Π (irbt black n₁) λ _ →
    --         Π 𝕂 λ _ →
    --         Π color λ y → Π nat λ n₂ → Π (irbt y n₂) λ _ →
    --         Π (U (meta (n₁ ≥ n₂))) λ _ →
    --         F (hrbt n₁)
    --       )
    --   joinRight' n₁ t₁ k y n₂ t₂ n₁≥n₂ with n₁ Nat.≟ n₂
    --   ... | yes refl = ret (hred (red t₁ k {!t₂!}))
    --   joinRight' .zero leaf k y .zero t₂ Nat.z≤n | no n₁≢n₂ = contradiction refl n₁≢n₂
    --   joinRight' .(suc _) (black t₁ k₁ t₃) k y .zero t₂ Nat.z≤n | no n₁≢n₂ = {!   !}
    --   joinRight' .(suc _) t₁ k y .(suc _) t₂ (Nat.s≤s n₁≥n₂) | no n₁≢n₂ = {!   !}
    --       -- call rotateLeftB


    -- unhiden : cmp (Π nat λ n → Π (hrbt n) λ _ → F (irbt black n))
    -- unhiden _ (hred (red x k x₁)) = ret {! black x k x₁  !}
    -- unhiden .(suc _) (hblack (black x k x₁)) = ret (black x k x₁)

    -- i-joinRight :
    --   cmp
    --     ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --       Π 𝕂 λ _ →
    --       Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --       Π (U (meta (n₁ ≥ n₂))) λ _ →
    --       F (irbt y₁ n₁)  -- TODO: is this correct?
    --     )
    -- i-joinRight y₁ n₁ t₁ k y₂ n₂ t₂ n₁≥n₂ with n₁ Nat.≟ n₂
    -- ... | yes refl = ret {!  red t₁ k t₂ !} -- black height are the same
    --                                          -- needs to make sure both y₁ and y₂ are black
    -- -- i-joinRight .black n₁ t₁ k .black n₂ t₂ n₁≥n₂ with n₁ Nat.≟ n₂
    -- -- ... | yes refl = ?
    -- i-joinRight .black .zero leaf k y₂ .zero t₂ Nat.z≤n | no n₁≢n₂ = contradiction refl n₁≢n₂
    -- i-joinRight .red n₁ (red t₁₁ k₁ t₁₂) k y₂ n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
    --   bind (F {!  !}) (i-joinRight _ _ t₁₂ k _ _ t₂ {!     !}) λ t₂' →
    --   ret (red t₁₁ k₁ t₂')
    -- i-joinRight .black .(suc _) (black t₁₁ k₁ t₁₂) k y₂ n₂ t₂ n₁≥n₂ | no n₁≢n₂ =
    --   {!   !}

    -- i-joinMid :
    --   cmp
    --     ( Π color λ y₁ → Π nat λ n₁ → Π (irbt y₁ n₁) λ _ →
    --       Π 𝕂 λ _ →
    --       Π color λ y₂ → Π nat λ n₂ → Π (irbt y₂ n₂) λ _ →
    --       F rbt
    --     )
    -- i-joinMid y₁ n₁ t₁ k y₂ n₂ t₂ with Nat.<-cmp n₁ n₂
    -- i-joinMid red n₁ t₁ k y₂ n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    -- i-joinMid black n₁ t₁ k red n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ k t₂) ⟫
    -- i-joinMid black n₁ t₁ k black n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (red t₁ k t₂) ⟫
    -- ... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ = {!   !}
    -- ... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
    --   bind (F rbt) (i-joinRight _ _ t₁ k _ _ t₂ (Nat.<⇒≤ n₁>n₂)) λ t →
    --   {!   !}

    joinMid : cmp (Π rbt λ _ → Π 𝕂 λ _ → Π rbt λ _ → F rbt)
    joinMid ⟪ t₁ ⟫ k ⟪ t₂ ⟫ = j-joinMid _ _ t₁ k _ _ t₂

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

    -- forget : cmp (Π nat λ n → Π (hrbt n) λ _ → F (arbt n))
    -- forget n (hred (red x k x₁)) = ret (at red x k x₁)
    -- forget .(suc _) (hblack (black x k x₁)) = ret (at black x k x₁)

    -- open StrictTotalOrder Key

    -- mutual
    --   ins-black : cmp (Π nat λ n → Π (irbt black n) λ _ → Π 𝕂 λ _ → F (hrbt n))
    --   ins-black .zero leaf k = ret (hred (red leaf k leaf))
    --   ins-black (suc n) (black t₁ k₁ t₂) k =
    --     case compare k k₁ of λ
    --       { (tri< k<k' ¬k≡k' ¬k>k') →
    --           bind (F (hrbt (suc n))) (ins n _ t₁ k) λ t₃ →
    --           bind (F (hrbt (suc n))) (rotateLeftB _ n t₃ k₁ t₂) ret
    --       ; (tri≈ ¬k<k' k≡k' ¬k>k') →
    --           bind (F (hrbt (suc n))) (ins n _ t₂ k) (λ t₃ →
    --           bind (F (hrbt (suc n))) {!  rotateRightB y₁ n t₁ k₁ t₃ !} ret)
    --       ; (tri> ¬k<k' ¬k≡k' k>k') → ret (hblack (black t₁ k t₂))
    --       }

    --   ins : cmp (Π nat λ n → Π color λ y → Π (irbt y n) λ _ → Π 𝕂 λ _ → F (arbt n))
    --   ins .zero .black leaf k =
    --     bind (F (arbt zero)) (ins-black zero leaf k) (λ x →
    --     bind (F (arbt zero)) (forget zero x) ret)
    --   ins n .red (red t k₁ t₁) k =
    --     case compare k k₁ of λ
    --       { (tri< k<k' ¬k≡k' ¬k>k') →
    --           bind (F (arbt n)) (ins-black n t k) λ t₂ →
    --           bind (F (arbt n)) (rotateLeftR black n t₂ k₁ t₁) ret
    --       ; (tri≈ ¬k<k' k≡k' ¬k>k') →
    --           bind (F (arbt n)) (ins-black n t₁ k) (λ t₂ →
    --           bind (F (arbt n)) (rotateRightR black n t k₁ t₂) ret)
    --       ; (tri> ¬k<k' ¬k≡k' k>k') → ret (at red t k t₁)
    --       }
    --   ins (suc n) .black (black t k₁ t₁) k =
    --     bind (F (arbt (suc n))) (ins-black (suc n) (black t k₁ t₁) k) λ x →
    --     bind (F (arbt (suc n))) (forget (suc n) x) ret

    -- unhiden' : cmp (Π nat λ n → Π (hrbt n) λ _ → F insrbt)
    -- unhiden' n (hred (red l k r)) = ret (root (black l k r))
    -- unhiden' .(suc _) (hblack (black l k r)) = ret (root (black l k r))

    -- insert : cmp (Π insrbt λ _ → Π 𝕂 λ _ → F insrbt)
    -- insert (root t) k =
    --   bind (F insrbt) (ins-black _ t k) λ ht →
    --   bind (F insrbt) (unhiden' _ ht) ret

module Ex/NatSet where
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

  open ParametricBST (ListBST strictTotalOrder)

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
