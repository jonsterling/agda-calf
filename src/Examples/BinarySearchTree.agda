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
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)

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
        bind (F (arrbt (suc n₁))) (jj-joinRight _ _ t₃ k _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred p) (≢-sym p₁))) λ { (redat t₄ k₂ leaf) → ret (blackat t₁ k₁ (red t₄ k₂ leaf))
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
        bind (F (hrbt (suc n₁))) (jj-joinRight _ _ t₃ k _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred p) (≢-sym p₁))) λ { (redat t₄ k₂ (red t₅ k₃ t₆)) → ret (redhd (red (black t₁ k₁ t₄) k₂ (black t₅ k₃ t₆))) -- rotate
                                                                           ; (redat t₄ k₂ leaf) → ret (blackhd (black t₁ k₁ (red t₄ k₂ leaf)))
                                                                           ; (redat t₄ k₂ (black t₅ k₃ t₆)) → ret (blackhd (black t₁ k₁ (red t₄ k₂ (black t₅ k₃ t₆))))
                                                                           ; (blackat t₄ k₂ t₅) → ret (blackhd (black t₁ k₁ (black t₄ k₂ t₅))) }

    record RBT : Set where
      pattern
      constructor ⟪_⟫
      field
        {y} : val color
        {n} : val nat
        t : val (irbt y n)
    rbt : tp pos
    rbt = U (meta RBT)

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
