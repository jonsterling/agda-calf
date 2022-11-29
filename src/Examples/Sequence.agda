{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Eq
open import Calf.Types.Nat
open import Data.Nat as N using (_+_)
open import Data.Nat.Properties as N
open import Calf.Types.Bounded costMonoid

open import Function

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)



import Algebra.Structures as A

variable
  A B C : tp pos
  X Y Z : tp neg
  P Q : val A → tp neg

lift₁ : cmp (Π A λ _ → X) → cmp (Π (U (F A)) λ _ → X)
lift₁ {X = X} f e = bind X e f

lift₂ : cmp (Π A λ _ → Π B λ _ → X) → cmp (Π (U (F A)) λ _ → Π (U (F B)) λ _ → X)
lift₂ {X = X} f e₁ e₂ = bind X e₁ λ v₁ → bind X e₂ λ v₂ → f v₁ v₂

record Pure (A : tp pos) : Set where
  field
    e : cmp (F A)
    v : ◯ (val A)
    h : (u : ext) → e ≡ ret (v u)

pure : tp pos → tp neg
pure A = meta (Pure A)

record SEQUENCE_CORE : Set₁ where
  field
    Seq : tp pos → tp pos

    -- data Seq (A : Set) : Set where
    --   singleton : A → Seq A
    --   empty : Seq A
    --   append : Seq A → Seq A → Seq A
    --   assoc : (x y z : Seq A) → append (append x y) z ≡ append x (append y z)
    --   idˡ : (x : Seq A) → append empty x ≡ x
    --   idʳ : (x : Seq A) → append x empty ≡ x

    singleton : cmp (Π A λ _ → pure (Seq A))
    empty : cmp (pure (Seq A))
    append : cmp (Π (Seq A) λ _ → Π (Seq A) λ _ → pure (Seq A))
    isMonoid : (u : ext) → A.IsMonoid _≡_ (λ s₁ s₂ → Pure.v (append {A} s₁ s₂) u) (Pure.v empty u)

    mapreduce :
      {X : tp neg}
      → (f : cmp (Π A λ _ → X))
      → (z : cmp X)
      → (g : cmp (Π (U X) λ _ → Π (U X) λ _ → X))
      → ◯ (A.IsMonoid _≡_ g z)
      → val (Seq A)
      → cmp X

    mapreduce/singleton : ∀ {f z g h a}     → (u : ext) → mapreduce {X = X} f z g h (Pure.v (singleton {A} a)  u) ≡ f a
    mapreduce/empty     : ∀ {f z g h}       → (u : ext) → mapreduce {X = X} f z g h (Pure.v (empty {A})        u) ≡ z
    mapreduce/append    : ∀ {f z g h s₁ s₂} → (u : ext) → mapreduce {X = X} f z g h (Pure.v (append {A} s₁ s₂) u) ≡ g (mapreduce {X = X} f z g h s₁) (mapreduce {X = X} f z g h s₂)

    induction :
      {P : ◯ (val (Seq A)) → tp neg}
      → cmp (Π A λ a → P λ u → Pure.v (singleton a) u)
      → (z : cmp (P λ u → Pure.v empty u))
      → (g : cmp (Π (Seq A) λ s₁ → Π (Seq A) λ s₂ → Π (U (P λ u → s₁)) λ _ → Π (U (P λ u → s₂)) λ _ → P λ u → Pure.v (append s₁ s₂) u))
      → ((u : ext) → cmp (Π (Seq A) λ s → Π (U (P λ u → s)) λ h → {!   !}))
      → (s : val (Seq A))
      → cmp (P λ u → s)

    -- induction/singleton : ∀ {P f z g h a}     → ◯ (dbind P (singleton {A} a ) (induction {P = P} f z g h) ≡ f a)
    -- induction/empty     : ∀ {P f z g h}       → ◯ (dbind P (empty {A}       ) (induction {P = P} f z g h) ≡ z)
    -- induction/append    : ∀ {P f z g h s₁ s₂} → ◯ (dbind P (append {A} s₁ s₂) (induction {P = P} f z g h) ≡ g s₁ s₂ (induction {P = P} f z g h s₁) (induction {P = P} f z g h s₂))

module Example (S : SEQUENCE_CORE) where
  open SEQUENCE_CORE S

  id-traverse : cmp (Π (Seq A) λ s → F (Seq A))
  id-traverse {A = A} =
    mapreduce
      {X = F (Seq A)}
      (λ a → Pure.e (singleton a))
      (Pure.e empty)
      (λ s₁ s₂ → lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂)) s₁ s₂)
      {!   !}
      -- λ u →
      --   Eq.subst₂
      --     (A.IsMonoid _≡_)
      --     -- (funext λ s₁ → funext λ s₂ →
      --     --   begin
      --     --     ret (Pure.v (lift₂ {X = pure (Seq A)} append s₁ s₂) u)
      --     --   ≡⟨ {!   !} ⟩
      --     --     Pure.e (lift₂ {X = pure (Seq A)} append s₁ s₂)
      --     --   ∎
      --     -- )
      --     -- (Eq.sym (Pure.h empty u))
      --     {!   !}
      --     {!   !}
      --     {! SEQUENCE_CORE.isMonoid S u  !}
        -- Eq.subst
        --   (λ e → A.IsMonoid _≡_ )
        -- {! begin_ ? ≡⟨ ? ⟩ ? _∎  !}
        -- where open ≡-Reasoning

  example₀ : ◯ (id-traverse {A = A} ≡ ret)
  example₀ {A = A} u = funext λ s →
    let open ≡-Reasoning in
    induction
      {P = λ s → meta (id-traverse (s u) ≡ ret (s u))}
      (λ a →
        begin
          id-traverse (Pure.v (singleton a) u)
        ≡⟨ mapreduce/singleton u ⟩
          Pure.e (singleton a)
        ≡⟨ Pure.h (singleton a) u ⟩
          ret (Pure.v (singleton a) u)
        ∎)
      ( begin
          id-traverse (Pure.v empty u)
        ≡⟨ mapreduce/empty u ⟩
          Pure.e empty
        ≡⟨ Pure.h empty u ⟩
          ret (Pure.v empty u)
        ∎
      )
      (λ s₁ s₂ ih₁ ih₂ →
          begin
            id-traverse (Pure.v (append s₁ s₂) u)
          ≡⟨ mapreduce/append u ⟩
            lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂)) (id-traverse s₁) (id-traverse s₂)
          ≡⟨ Eq.cong₂ (lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂))) ih₁ ih₂ ⟩
            lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂)) (ret {Seq A} s₁) (ret {Seq A} s₂)
          ≡⟨⟩
            Pure.e (append s₁ s₂)
          ≡⟨ Pure.h (append s₁ s₂) u ⟩
            ret (Pure.v (append s₁ s₂) u)
          ∎
        )
      {!   !}
      s

  -- map : cmp (Π (U (Π A λ _ → F B)) λ _ → Π (Seq A) λ _ → F (Seq B))
  -- map {B = B} f =
  --   mapreduce {X = F (Seq B)}
  --     (lift₁ {X = F (Seq B)} singleton ∘ f)
  --     empty
  --     (lift₂ {X = F (Seq B)} append)
  --     (isMonoid S)

  -- sum : cmp (Π (Seq nat) λ _ → F nat)
  -- sum =
  --   mapreduce {X = F nat}
  --     ret
  --     (ret 0)
  --     (lift₂ {X = F nat} λ n₁ n₂ → ret (n₁ + n₂))
  --     record
  --       { isSemigroup =
  --           record
  --             { isMagma =
  --               record { isEquivalence =
  --                   record
  --                     { refl = λ u → refl
  --                     ; sym = λ h u → Eq.sym (h u)
  --                     ; trans = λ h₁ h₂ u → Eq.trans (h₁ u) (h₂ u)
  --                     }
  --                 ; ∙-cong = λ h₁ h₂ u → Eq.cong₂ (lift₂ (λ n₁ n₂ → ret (n₁ + n₂))) (h₁ u) (h₂ u)
  --                 }
  --               ; assoc = λ n₁ n₂ n₃ u → Eq.cong (bind (F (U (meta ℕ))) n₁) (funext (λ v₁ → Eq.cong (bind (F nat) n₂) (funext (λ v₂ → Eq.cong (bind (F nat) n₃) (funext (λ v₃ → Eq.cong ret (+-assoc v₁ v₂ v₃))))))) }
  --               ; identity = (λ n u → {!   !}) , λ n u → {!   !} }

  -- reverse : cmp (Π (Seq A) λ _ → F (Seq A))
  -- reverse {A = A} =
  --   mapreduce {X = F (Seq A)}
  --     singleton
  --     empty
  --     (λ s₁ s₂ → lift₂ {X = F (Seq A)} append s₂ s₁)
  --     {!   !}

  -- example₁ : (f : cmp (Π A λ _ → F B)) (s : val (Seq A)) → lift₁ {X = F (Seq B)} (map f) (reverse s) ≡ lift₁ {X = F (Seq B)} reverse (map f s)
  -- example₁ = {!   !}

  -- example₂ : (s : val (Seq nat)) → bind (F nat) (reverse s) sum ≡ sum s
  -- example₂ = {!   !}
