{-# OPTIONS --prop --rewriting #-}

module Examples.BinarySearchTree where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (zero to 𝟘; _+_ to _⊕_)

open import Level using (0ℓ)

open import Calf costMonoid
open import Calf.Types.Unit
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Bool
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Bounded costMonoid
open import Data.String using (String)
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_; _∸_)
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


-- Middle Sequence
record MSequence : Set where
  field
    seq : tp pos → tp pos

    empty : cmp (F (seq A))
    join : cmp (Π (seq A) λ s₁ → Π A λ a → Π (seq A) λ s₂ → F (seq A))

    rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (seq A) λ _ → Π (U X) λ _ → Π A λ _ → Π (seq A) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (seq A) λ _ → X
        )


ListMSequence : MSequence
ListMSequence =
  record
    { seq = list
    ; empty = ret []
    ; join =
        λ {A} l₁ a l₂ →
          let n = length l₁ + 1 + length l₂ in
          step (F (list A)) n (ret (l₁ ++ [ a ] ++ l₂))
    ; rec = λ {A} {X} → rec {A} {X}
    }
  where
    rec : {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (list A) λ _ → Π (U X) λ _ → Π A λ _ → Π (list A) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (list A) λ _ → X
        )
    rec {A} {X} z f []      = z
    rec {A} {X} z f (x ∷ l) = step X 1 (f [] z x l (rec {A} {X} z f l))


RedBlackMSequence : MSequence
RedBlackMSequence =
  record
    { seq = rbt
    ; empty = ret ⟪ leaf ⟫
    ; join = join
    ; rec = λ {A} {X} → rec {A} {X}
    }
  where
    data Color : Set where
      red : Color
      black : Color
    color : tp pos
    color = U (meta Color)

    -- Indexed Red Black Tree
    data IRBT (A : tp pos) : val color → val nat → Set where
      leaf  : IRBT A black zero
      red   : {n : val nat}
        (t₁ : IRBT A black n) (a : val A) (t₂ : IRBT A black n)
        → IRBT A red n
      black : {n : val nat} {y₁ y₂ : val color}
        (t₁ : IRBT A y₁ n) (a : val A) (t₂ : IRBT A y₂ n)
        → IRBT A black (suc n)
    irbt : tp pos → val color → val nat → tp pos
    irbt A y n = U (meta (IRBT A y n))

    record RBT (A : tp pos) : Set where
      pattern
      constructor ⟪_⟫
      field
        {y} : val color
        {n} : val nat
        t : val (irbt A y n)
    rbt : tp pos → tp pos
    rbt A = U (meta (RBT A))


    data AlmostLeftRBT (A : tp pos) : (right-color : val color) → val nat → Set where
      violation :
        {n : val nat}
        → IRBT A red n → val A → IRBT A black n
        → AlmostLeftRBT A red n
      valid :
        {right-color : val color} {n : val nat} {y : val color} → IRBT A y n
        → AlmostLeftRBT A right-color n
    alrbt : tp pos → val color → val nat → tp pos
    alrbt A y n = U (meta (AlmostLeftRBT A y n))

    joinLeft :
      cmp
        ( Π color λ y₁ → Π nat λ n₁ → Π (irbt A y₁ n₁) λ _ →
          Π A λ _ →
          Π color λ y₂ → Π nat λ n₂ → Π (irbt A y₂ n₂) λ _ →
          Π (U (meta (n₁ < n₂))) λ _ →
          F (alrbt A y₂ n₂)
        )
    joinLeft {A} y₁ n₁ t₁ a .red n₂ (red t₂₁ a₁ t₂₂) n₁<n₂ =
      step (F (alrbt A red n₂)) 1 $
      bind (F (alrbt A red n₂)) (joinLeft _ _ t₁ a _ _ t₂₁ n₁<n₂) λ
        { (valid {y = red} t') → ret (violation t' a₁ t₂₂)
        ; (valid {y = black} t') → ret (valid (red t' a₁ t₂₂)) }
    joinLeft {A} y₁ n₁ t₁ a .black (suc n₂) (black t₂₁ a₁ t₂₂) n₁<n₂ with n₁ Nat.≟ n₂
    joinLeft red n₁ (red t₁₁ a₁ t₁₂) a .black (suc n₁) (black t₂₁ a₂ t₂₂) n₁<n₂ | yes refl =
      ret (valid (red (black t₁₁ a₁ t₁₂) a (black t₂₁ a₂ t₂₂)))
    joinLeft black n₁ t₁ a .black (suc n₂) (black {y₁ = red} (red t₂₁₁ a₁₁ t₂₁₂) a₁ t₂₂) n₁<n₂ | yes refl =
      ret (valid (red (black t₁ a t₂₁₁) a₁₁ (black t₂₁₂ a₁ t₂₂)))
    joinLeft black n₁ t₁ a .black (suc n₂) (black {y₁ = black} t₂₁ a₁ t₂₂) n₁<n₂ | yes refl =
      ret (valid (black (red t₁ a t₂₁) a₁ t₂₂))
    ... | no n₁≢n₂ =
      step (F (alrbt A black (suc n₂))) 1 $
      bind (F (alrbt A black (suc n₂))) (joinLeft _ _ t₁ a _ _ t₂₁ (Nat.≤∧≢⇒< (Nat.≤-pred n₁<n₂) n₁≢n₂)) λ
        { (violation (red t'₁₁ a'₁ t'₁₂) a' t'₂) → ret (valid (red (black t'₁₁ a'₁ t'₁₂) a' (black t'₂ a₁ t₂₂)))
        ; (valid t') → ret (valid (black t' a₁ t₂₂)) }

    joinLeft/cost : (y : val color) (n₁ n₂ : val nat) → ℂ
    joinLeft/cost red n₁ n₂ = 1 + (2 * (n₂ ∸ n₁))
    joinLeft/cost black n₁ n₂ = (2 * (n₂ ∸ n₁))

    joinLeft/is-bounded' : ∀ y₁ n₁ t₁ a y₂ n₂ t₂ n₁<n₂
        → IsBounded (alrbt A y₂ n₂) (joinLeft y₁ n₁ t₁ a y₂ n₂ t₂ n₁<n₂) (joinLeft/cost y₂ n₁ n₂)

    joinLeft/is-bounded : ∀ {A} y₁ n₁ t₁ a y₂ n₂ t₂ n₁<n₂
        → IsBounded (alrbt A y₂ n₂) (joinLeft y₁ n₁ t₁ a y₂ n₂ t₂ n₁<n₂) (1 + (2 * (n₂ ∸ n₁)))

    joinLeft/is-bounded' {A} y₁ n₁ t₁ a .red n₂ (red t₂₁ a₁ t₂₂) n₁<n₂ =
      bound/step 1 (2 * (n₂ ∸ n₁))
      (Eq.subst
        (IsBounded _ _)
        (Nat.+-identityʳ (2 * (n₂ ∸ n₁)))
        (bound/bind/const (2 * (n₂ ∸ n₁)) 0
          (joinLeft/is-bounded' _ _ t₁ a _ _ t₂₁ n₁<n₂)
          λ { (valid (red _ _ _)) → bound/ret
            ; (valid (black _ _ _)) → bound/ret }))
    joinLeft/is-bounded' y₁ n₁ t₁ a .black (suc n₂) (black t₂₁ a₁ t₂₂) n₁<n₂ with n₁ Nat.≟ n₂
    joinLeft/is-bounded' red _ (red _ _ _) _ .black _ (black _ _ _) _ | yes refl =
      bound/relax (λ u → Nat.z≤n) bound/ret
    joinLeft/is-bounded' black _ _ _ .black _ (black {y₁ = red} (red _ _ _) _ _) _ | yes refl =
      bound/relax (λ u → Nat.z≤n) bound/ret
    joinLeft/is-bounded' black _ _ _ .black _ (black {y₁ = black} _ _ _) _ | yes refl =
      bound/relax (λ u → Nat.z≤n) bound/ret
    ...| no n₁≢n₂ =
      Eq.subst
        (IsBounded _ _) {x = 2 + 2 * (n₂ ∸ n₁)}
        (Eq.trans (Eq.sym (Nat.*-suc 2 (n₂ ∸ n₁))) (Eq.cong (2 *_) (Eq.sym (Nat.+-∸-assoc 1 (Nat.≤-pred n₁<n₂)))))
        (bound/step 1 (1 + 2 * (n₂ ∸ n₁))
          (Eq.subst
            (IsBounded _ _) {x = 1 + (2 * (n₂ ∸ n₁)) + 0}
            (Nat.+-identityʳ (1 + 2 * (n₂ ∸ n₁)))
            (bound/bind/const (1 + (2 * (n₂ ∸ n₁))) 0
              (joinLeft/is-bounded _ _ t₁ a _ _ t₂₁ _)
              λ { (violation (red _ _ _) _ _) → bound/ret
                ; (valid _) → bound/ret })))

    joinLeft/is-bounded y₁ n₁ t₁ a red n₂ t₂ n₁<n₂ =
      joinLeft/is-bounded' y₁ n₁ t₁ a red n₂ t₂ n₁<n₂
    joinLeft/is-bounded y₁ n₁ t₁ a black n₂ t₂ n₁<n₂ =
      bound/relax (λ u → Nat.n≤1+n _) (joinLeft/is-bounded' y₁ n₁ t₁ a black n₂ t₂ n₁<n₂)

    data AlmostRightRBT (A : tp pos) : (left-color : val color) → val nat → Set where
      violation :
        {n : val nat}
        → IRBT A black n → val A → IRBT A red n
        → AlmostRightRBT A red n
      valid :
        {left-color : val color} {n : val nat} {y : val color} → IRBT A y n
        → AlmostRightRBT A left-color n
    arrbt : tp pos → val color → val nat → tp pos
    arrbt A y n = U (meta (AlmostRightRBT A y n))

    joinRight :
      cmp
        ( Π color λ y₁ → Π nat λ n₁ → Π (irbt A y₁ n₁) λ _ →
          Π A λ _ →
          Π color λ y₂ → Π nat λ n₂ → Π (irbt A y₂ n₂) λ _ →
          Π (U (meta (n₁ > n₂))) λ _ →
          F (arrbt A y₁ n₁)
        )
    joinRight {A} .red n₁ (red t₁₁ a₁ t₁₂) a y₂ n₂ t₂ n₁>n₂ =
      step (F (arrbt A red n₁)) 1 $
      bind (F (arrbt A red n₁)) (joinRight _ _ t₁₂ a _ _ t₂ n₁>n₂) λ
        { (valid {y = red} t') → ret (violation t₁₁ a₁ t')
        ; (valid {y = black} t') → ret (valid (red t₁₁ a₁ t')) }
    joinRight {A} .black (suc n₁) (black t₁₁ a₁ t₁₂) a y₂ n₂ t₂ n₁>n₂ with n₁ Nat.≟ n₂
    joinRight .black (suc n₁) (black t₁₁ a₁ t₁₂) a red n₁ (red t₂₁ a₂ t₂₂) n₁>n₂ | yes refl =
      ret (valid (red (black t₁₁ a₁ t₁₂) a (black t₂₁ a₂ t₂₂)))
    joinRight .black (suc n₁) (black {y₂ = red} t₁₁ a₁ (red t₁₂₁ a₁₂ t₁₂₂)) a black n₁ t₂ n₁>n₂ | yes refl =
      ret (valid (red (black t₁₁ a₁ t₁₂₁) a₁₂ (black t₁₂₂ a t₂)))
    joinRight .black (suc n₁) (black {y₂ = black} t₁₁ a₁ t₁₂) a black n₁ t₂ n₁>n₂ | yes refl =
      ret (valid (black t₁₁ a₁ (red t₁₂ a t₂)))
    ... | no n₁≢n₂ =
      step (F (arrbt A black (suc n₁))) 1 $
      bind (F (arrbt A black (suc n₁))) (joinRight _ _ t₁₂ a _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred n₁>n₂) (≢-sym n₁≢n₂))) λ
        { (violation t'₁ a' (red t'₂₁ a'₂ t'₂₂)) → ret (valid (red (black t₁₁ a₁ t'₁) a' (black t'₂₁ a'₂ t'₂₂)))
        ; (valid t') → ret (valid (black t₁₁ a₁ t'))  }

    joinRight/cost : (y : val color) (n₁ n₂ : val nat) → ℂ
    joinRight/cost red n₁ n₂ = 1 + (2 * (n₁ ∸ n₂))
    joinRight/cost black n₁ n₂ = (2 * (n₁ ∸ n₂))

    joinRight/is-bounded' : ∀ y₁ n₁ t₁ a y₂ n₂ t₂ n₁>n₂
        → IsBounded (arrbt A y₁ n₁) (joinRight y₁ n₁ t₁ a y₂ n₂ t₂ n₁>n₂) (joinRight/cost y₁ n₁ n₂)

    joinRight/is-bounded : ∀ {A} y₁ n₁ t₁ a y₂ n₂ t₂ n₁>n₂
        → IsBounded (arrbt A y₁ n₁) (joinRight y₁ n₁ t₁ a y₂ n₂ t₂ n₁>n₂) (1 + (2 * (n₁ ∸ n₂)))

    joinRight/is-bounded' red n₁ (red t₁₁ a₁ t₁₂) a y₂ n₂ t₂ n₁>n₂ =
      bound/step 1 (2 * (n₁ ∸ n₂))
      (Eq.subst
        (IsBounded _ _)
        (Nat.+-identityʳ (2 * (n₁ ∸ n₂)))
        (bound/bind/const (2 * (n₁ ∸ n₂)) 0
          (joinRight/is-bounded' _ _ t₁₂ a _ _ t₂ n₁>n₂)
          (λ {(valid (red _ _ _)) → bound/ret
            ; (valid (black _ _ _)) → bound/ret })))
    joinRight/is-bounded' black (suc n₁) (black t₁₁ a₁ t₁₂) a y₂ n₂ t₂ n₁>n₂ with n₁ Nat.≟ n₂
    joinRight/is-bounded' black _ (black _ _ _) _ red _ (red _ _ _) _ | yes refl =
      bound/relax (λ u → Nat.z≤n) bound/ret
    joinRight/is-bounded' black _ (black {y₂ = red} _ _ (red _ _ _)) _ black _ _ _ | yes refl =
      bound/relax (λ u → Nat.z≤n) bound/ret
    joinRight/is-bounded' black _ (black {y₂ = black} _ _ _) _ black _ _ _ | yes refl =
      bound/relax (λ u → Nat.z≤n) bound/ret
    ... | no n₁≢n₂ =
      Eq.subst
        (IsBounded _ _) {x = 2 + 2 * (n₁ ∸ n₂)}
        (Eq.trans (Eq.sym (Nat.*-suc 2 (n₁ ∸ n₂))) (Eq.cong (2 *_) (Eq.sym (Nat.+-∸-assoc 1 n₁>n₂))))
        (bound/step 1 (1 + 2 * (n₁ ∸ n₂))
          (Eq.subst
            (IsBounded _ _) {x = 1 + 2 * (n₁ ∸ n₂) + 0}
            (Nat.+-identityʳ (1 + 2 * (n₁ ∸ n₂)))
            (bound/bind/const (1 + 2 * (n₁ ∸ n₂)) 0
              (joinRight/is-bounded _ _ t₁₂ a _ _ t₂ _)
              λ { (violation _ _ (red _ _ _)) → bound/ret
                ; (valid _) → bound/ret })))

    joinRight/is-bounded red n₁ t₁ a y₂ n₂ t₂ n₁>n₂ =
      joinRight/is-bounded' red n₁ t₁ a y₂ n₂ t₂ n₁>n₂
    joinRight/is-bounded black n₁ t₁ a y₂ n₂ t₂ n₁>n₂ =
      bound/relax (λ u → Nat.n≤1+n _) (joinRight/is-bounded' black n₁ t₁ a y₂ n₂ t₂ n₁>n₂)

    i-join :
      cmp
        ( Π color λ y₁ → Π nat λ n₁ → Π (irbt A y₁ n₁) λ _ →
          Π A λ _ →
          Π color λ y₂ → Π nat λ n₂ → Π (irbt A y₂ n₂) λ _ →
          F (rbt A)
        )
    i-join {A} y₁ n₁ t₁ a y₂ n₂ t₂ with Nat.<-cmp n₁ n₂
    i-join red n₁ t₁ a y₂ n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ a t₂) ⟫
    i-join black n₁ t₁ a red n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (black t₁ a t₂) ⟫
    i-join black n₁ t₁ a black n₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ = ret ⟪ (red t₁ a t₂) ⟫
    ... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ =
      bind (F (rbt A)) (joinLeft _ _ t₁ a _ _ t₂ n₁<n₂) λ
        { (violation t'₁ a' t'₂) → ret ⟪ (black t'₁ a' t'₂) ⟫
        ; (valid t') → ret ⟪ t' ⟫}
    ... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
      bind (F (rbt A)) (joinRight _ _ t₁ a _ _ t₂ n₁>n₂) λ
        { (violation t'₁ a' t'₂) → ret ⟪ black t'₁ a' t'₂ ⟫
        ; (valid t') → ret ⟪ t' ⟫ }

    i-join/is-bounded : ∀ {A} y₁ n₁ t₁ a y₂ n₂ t₂
        → IsBounded (rbt A) (i-join y₁ n₁ t₁ a y₂ n₂ t₂) (1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)))
    i-join/is-bounded {A} y₁ n₁ t₁ a y₂ n₂ t₂ with Nat.<-cmp n₁ n₂
    i-join/is-bounded {A} red n₁ t₁ a y₂ .n₁ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
      bound/relax (λ u → Nat.z≤n) bound/ret
    i-join/is-bounded {A} black n₁ t₁ a red n₁ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
      bound/relax (λ u → Nat.z≤n) bound/ret
    i-join/is-bounded {A} black n₁ t₁ a black n₁ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
      bound/relax (λ u → Nat.z≤n) bound/ret
    ... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ =
      Eq.subst
        (IsBounded _ _) {x = 1 + 2 * (n₂ ∸ n₁) + 0}
        (Eq.cong suc (Eq.trans (Nat.+-identityʳ (2 * (n₂ ∸ n₁))) (Eq.cong (2 *_) (Eq.cong₂ (λ x y → x ∸ y) (Eq.sym (Nat.m≤n⇒m⊔n≡n (Nat.<⇒≤ n₁<n₂))) (Eq.sym (Nat.m≤n⇒m⊓n≡m (Nat.<⇒≤ n₁<n₂)))))))
        (bound/bind/const (1 + 2 * (n₂ ∸ n₁)) 0
          (joinLeft/is-bounded _ _ t₁ a _ _ t₂ n₁<n₂)
          λ { (violation _ _ _) → bound/ret
            ; (valid _) → bound/ret })
    ... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
      Eq.subst
        (IsBounded _ _) {x = 1 + 2 * (n₁ ∸ n₂) + 0}
        (Eq.cong suc (Eq.trans (Nat.+-identityʳ (2 * (n₁ ∸ n₂))) (Eq.cong (2 *_) (Eq.cong₂ (λ x y → x ∸ y) (Eq.sym (Nat.m≥n⇒m⊔n≡m (Nat.<⇒≤ n₁>n₂))) (Eq.sym (Nat.m≥n⇒m⊓n≡n (Nat.<⇒≤ n₁>n₂)))))))
        (bound/bind/const (1 + 2 * (n₁ ∸ n₂)) 0
          (joinRight/is-bounded _ _ t₁ a _ _ t₂ n₁>n₂)
          λ { (violation _ _ _) → bound/ret
            ; (valid _) → bound/ret })

    join : cmp (Π (rbt A) λ _ → Π A λ _ → Π (rbt A) λ _ → F (rbt A))
    join ⟪ t₁ ⟫ a ⟪ t₂ ⟫ = i-join _ _ t₁ a _ _ t₂

    join/is-bounded : ∀ {A} t₁ a t₂ → IsBounded (rbt A) (join t₁ a t₂) (1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)))
    join/is-bounded {A} ⟪ t₁ ⟫ a ⟪ t₂ ⟫ = i-join/is-bounded _ _ t₁ a _ _ t₂

    i-rec : {A : tp pos} {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π
            ( U
              ( Π color λ y₁ → Π nat λ n₁ → Π (irbt A y₁ n₁) λ _ → Π (U X) λ _ →
                Π A λ _ →
                Π color λ y₂ → Π nat λ n₂ → Π (irbt A y₂ n₂) λ _ → Π (U X) λ _ →
                X
              )
            ) λ _ →
          Π color λ y → Π nat λ n → Π (irbt A y n) λ _ →
          X
        )
    i-rec {A} {X} z f .black .zero    leaf            = z
    i-rec {A} {X} z f .red   n        (red   t₁ a t₂) =
      f
        _ _ t₁ (i-rec {A} {X} z f _ _ t₁)
        a
        _ _ t₂ (i-rec {A} {X} z f _ _ t₂)
    i-rec {A} {X} z f .black .(suc _) (black t₁ a t₂) =
      f
        _ _ t₁ (i-rec {A} {X} z f _ _ t₁)
        a
        _ _ t₂ (i-rec {A} {X} z f _ _ t₂)

    rec : {A : tp pos} {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (rbt A) λ _ → Π (U X) λ _ → Π A λ _ → Π (rbt A) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (rbt A) λ _ → X
        )
    rec {A} {X} z f ⟪ t ⟫ =
      i-rec {A} {X}
        z
        (λ _ _ t₁ ih₁ a _ _ t₂ ih₂ → f ⟪ t₁ ⟫ ih₁ a ⟪ t₂ ⟫ ih₂)
        _ _ t


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
