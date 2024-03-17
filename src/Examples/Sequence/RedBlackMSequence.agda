{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.RedBlackMSequence where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid

open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.Product
open import Calf.Data.Sum
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid

open import Data.Nat as Nat using (_+_; _*_; ⌊_/2⌋; _≥_; _∸_)
import Data.Nat.Properties as Nat
open import Data.Nat.Logarithm

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

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
    record RBT (A : tp⁺) : Set where
      pattern
      constructor ⟪_⟫
      field
        {y} : val color
        {n} : val nat
        {l} : val (list A)
        t : val (irbt A y n l)
    rbt : (A : tp⁺) → tp⁺
    rbt A = meta⁺ (RBT A)

    joinCont : ∀ (t₁ : RBT A) (t₂ : RBT A) a → Σ Color (λ c → Σ (List (val A)) (λ l → Σ (l ≡ (RBT.l t₁ ++ [ a ] ++ RBT.l t₂)) (λ x →
        IRBT A c (suc (RBT.n t₁ ⊔ RBT.n t₂)) l ⊎ IRBT A c (RBT.n t₁ ⊔ RBT.n t₂) l))) → cmp (F (rbt A))
    joinCont _ _ _ (_ , _ , _ , inj₁ t) = ret ⟪ t ⟫
    joinCont _ _ _ (_ , _ , _ , inj₂ t) = ret ⟪ t ⟫

    join : cmp (Π (rbt A) λ _ → Π A λ _ → Π (rbt A) λ _ → F (rbt A))
    join {A} t₁ a t₂ = bind (F (rbt A)) (i-join _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂)) (joinCont t₁ t₂ a)

    join/is-bounded : ∀ {A} t₁ a t₂ → IsBounded (rbt A) (join t₁ a t₂)
      (1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)) , 1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)))
    join/is-bounded {A} t₁ a t₂ =
      let open ≤⁻-Reasoning cost in
        begin
          bind cost (
            bind (F (rbt A)) (i-join _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂)) (joinCont t₁ t₂ a))
          (λ _ → ret triv)
        ≡⟨ Eq.cong
             (λ f → bind cost (i-join _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂)) f)
             (funext (λ { (_ , _ , _ , inj₁ _) → refl
                        ; (_ , _ , _ , inj₂ _) → refl })) ⟩
          bind cost (i-join _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂)) (λ _ → ret triv)
        ≤⟨ i-join/is-bounded _ _ _ (RBT.t t₁) a _ _ _ (RBT.t t₂) ⟩
          step⋆ (1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)) , 1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)))
        ∎

    nodes : RBT A → val nat
    nodes ⟪ t ⟫ = i-nodes t

    nodes/upper-bound : (t : RBT A) → RBT.n t Nat.≤ ⌈log₂ (1 + (nodes t)) ⌉
    nodes/upper-bound ⟪ t ⟫ = i-nodes/bound/log-node-black-height t

    nodes/lower-bound : (t : RBT A) → RBT.n t Nat.≥ ⌊ (⌈log₂ (1 + (nodes t)) ⌉ ∸ 1) /2⌋
    nodes/lower-bound ⟪ t ⟫ = i-nodes/lower-bound/log-node-black-height t 

    join/cost : ∀ {A} (t₁ : RBT A) (t₂ : RBT A) → ℂ
    join/cost {A} t₁ t₂ =
      let max = ⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ in
      let min = ⌊ (⌈log₂ (1 + (nodes t₁)) ⌉ ∸ 1) /2⌋ Nat.⊓ ⌊ (⌈log₂ (1 + (nodes t₂)) ⌉ ∸ 1) /2⌋ in
        (1 + 2 * (max ∸ min)) , (1 + 2 * (max ∸ min))

    join/is-bounded/nodes : ∀ {A} t₁ a t₂ → IsBounded (rbt A) (join t₁ a t₂) (join/cost t₁ t₂)
    join/is-bounded/nodes {A} t₁ a t₂ =
      let open ≤⁻-Reasoning cost in
        begin
          bind cost (join t₁ a t₂) (λ _ → ret triv)
        ≤⟨ join/is-bounded t₁ a t₂ ⟩
          step⋆ (1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)) , 1 + (2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)))
        ≤⟨ step⋆-mono-≤⁻ (black-height-cost/to/node-cost , black-height-cost/to/node-cost)  ⟩
          step⋆ (join/cost t₁ t₂)
        ∎
          where
            black-height-cost/to/node-cost : 1 + 2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂) Nat.≤ 1 + 2 * (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ ∸ ⌊ (⌈log₂ (1 + (nodes t₁)) ⌉ ∸ 1) /2⌋ Nat.⊓ ⌊ (⌈log₂ (1 + (nodes t₂)) ⌉ ∸ 1) /2⌋)
            black-height-cost/to/node-cost =
              let open Nat.≤-Reasoning in
                begin
                  1 + 2 * (RBT.n t₁ Nat.⊔ RBT.n t₂ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)
                ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.*-monoʳ-≤ 2 (Nat.∸-monoˡ-≤ (RBT.n t₁ Nat.⊓ RBT.n t₂) (Nat.⊔-mono-≤ (nodes/upper-bound t₁) (nodes/upper-bound t₂)))) ⟩
                  1 + 2 * (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ ∸ RBT.n t₁ Nat.⊓ RBT.n t₂)
                ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.*-monoʳ-≤ 2 (Nat.∸-monoʳ-≤ (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉) (Nat.⊓-mono-≤ (nodes/lower-bound t₁) (nodes/lower-bound t₂)))) ⟩
                  1 + 2 * (⌈log₂ (1 + (nodes t₁)) ⌉ Nat.⊔ ⌈log₂ (1 + (nodes t₂)) ⌉ ∸ ⌊ (⌈log₂ (1 + (nodes t₁)) ⌉ ∸ 1) /2⌋ Nat.⊓ ⌊ (⌈log₂ (1 + (nodes t₂)) ⌉ ∸ 1) /2⌋)
                ∎

    rec : {A : tp⁺} {X : tp⁻} →
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
