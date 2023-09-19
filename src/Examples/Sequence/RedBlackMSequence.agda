{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.RedBlackMSequence where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid renaming (zero to 𝟘; _+_ to _⊕_)

open import Calf costMonoid
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Bounded costMonoid

open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_; _∸_)
import Data.Nat.Properties as Nat
open import Data.Nat.Logarithm
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)


open import Examples.Sequence.MSequence
open import Examples.Sequence.RedBlackTree


RedBlackMSequence : MSequence
RedBlackMSequence =
  record
    { seq = rbt
    ; empty = ret ⟪ leaf ⟫
    ; join = join
    ; rec = λ {A} {X} → rec {A} {X}
    }
  where
    record RBT (A : tp pos) : Set where
      pattern
      constructor ⟪_⟫
      field
        {y} : val color
        {n} : val nat
        {l} : val (list A)
        t : val (irbt A y n l)
    rbt : (A : tp pos) → tp pos
    rbt A = U (meta (RBT A))

    join : cmp (Π (rbt A) λ _ → Π A λ _ → Π (rbt A) λ _ → F (rbt A))
    join {A} t₁ a t₂ = bind (F (rbt A)) (i-join _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂)) λ { (_ , _ , _ , inj₁ t) → ret ⟪ t ⟫
                                                                                       ; (_ , _ , _ , inj₂ t) → ret ⟪ t ⟫ }

    join/is-bounded : ∀ {A} t₁ a t₂ → IsBounded (rbt A) (join t₁ a t₂) (1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)))
    join/is-bounded {A} t₁ a t₂ =
      Eq.subst
        (IsBounded _ _) {x = 1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)) + 0}
        (Eq.cong suc (Nat.+-identityʳ (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂))))
        (bound/bind/const (1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂))) 0
          (i-join/is-bounded _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂))
          (λ { (_ , _ , _ , inj₁ t) → bound/ret
             ; (_ , _ , _ , inj₂ t) → bound/ret}))

    nodes : RBT A → val nat
    nodes ⟪ t ⟫ = i-nodes t

    nodes/bound/log-node-black-height : (t : RBT A) → RBT.n t ≤ ⌈log₂ (1 + (nodes t)) ⌉
    nodes/bound/log-node-black-height ⟪ t ⟫ = i-nodes/bound/log-node-black-height t

    nodes/lower-bound/log-node-black-height : (t : RBT A) → RBT.n t ≥ ⌊ (⌈log₂ (1 + (nodes t)) ⌉ ∸ 1) /2⌋
    nodes/lower-bound/log-node-black-height ⟪ t ⟫ = i-nodes/lower-bound/log-node-black-height t 

    join/cost : ∀ {A} (t₁ : RBT A) (t₂ : RBT A) → ℂ
    join/cost {A} t₁ t₂ =
      let max = ⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ in
      let min = ⌊ (⌈log₂ (1 + (nodes t₁)) ⌉ ∸ 1) /2⌋ Nat.⊓ ⌊ (⌈log₂ (1 + (nodes t₂)) ⌉ ∸ 1) /2⌋ in
        1 + 2 * (max ∸ min)

    join/is-bounded/nodes : ∀ {A} t₁ a t₂ → IsBounded (rbt A) (join t₁ a t₂) (join/cost t₁ t₂)
    join/is-bounded/nodes {A} t₁ a t₂ =
      bound/relax
        (λ u →
          let open ≤-Reasoning in
            begin
              1 + 2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)
            ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.*-monoʳ-≤ 2 (Nat.∸-monoˡ-≤ (RBT.n t₁ Nat.⊓ RBT.n t₂) (Nat.⊔-mono-≤ (nodes/bound/log-node-black-height t₁) (nodes/bound/log-node-black-height t₂)))) ⟩
              1 + 2 * (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)
            ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.*-monoʳ-≤ 2 (Nat.∸-monoʳ-≤ (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉) (Nat.⊓-mono-≤ (nodes/lower-bound/log-node-black-height t₁) (nodes/lower-bound/log-node-black-height t₂)))) ⟩
              1 + 2 * (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ ∸ ⌊ (⌈log₂ (1 + (nodes t₁)) ⌉ ∸ 1) /2⌋ Nat.⊓ ⌊ (⌈log₂ (1 + (nodes t₂)) ⌉ ∸ 1) /2⌋)
            ≡⟨⟩
              join/cost t₁ t₂
            ∎
        )
        (join/is-bounded t₁ a t₂)

    rec : {A : tp pos} {X : tp neg} →
      cmp
        ( Π (U X) λ _ →
          Π (U (Π (rbt A) λ _ → Π (U X) λ _ → Π A λ _ → Π (rbt A) λ _ → Π (U X) λ _ → X)) λ _ →
          Π (rbt A) λ _ → X
        )
    rec {A} {X} z f ⟪ t ⟫ =
      i-rec {A} {X}
        z
        (λ _ _ _ t₁ ih₁ a _ _ _ t₂ ih₂ → f ⟪ t₁ ⟫ ih₁ a ⟪ t₂ ⟫ ih₂)
        _ _ _ t
