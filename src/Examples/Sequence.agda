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
open import Calf.Types.Bounded costMonoid

open import Function

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)



import Algebra.Structures as A

variable
  A B C : tp pos
  X Y Z : tp neg
  P Q : val A → tp neg

_≅_ : cmp X → cmp X → Set
x ≅ y = ◯ (x ≡ y)

lift₁ : cmp (Π A λ _ → X) → cmp (Π (U (F A)) λ _ → X)
lift₁ {X = X} f e = bind X e f

lift₂ : cmp (Π A λ _ → Π B λ _ → X) → cmp (Π (U (F A)) λ _ → Π (U (F B)) λ _ → X)
lift₂ {X = X} f e₁ e₂ = bind X e₁ λ v₁ → bind X e₂ λ v₂ → f v₁ v₂

record SEQUENCE_CORE : Set₁ where
  field
    Seq : tp pos → tp pos  -- should this be tp neg?

    -- data Seq (A : Set) : Set where
    --   singleton : A → Seq A
    --   empty : Seq A
    --   append : Seq A → Seq A → Seq A
    --   assoc : (x y z : Seq A) → append (append x y) z ≡ append x (append y z)
    --   idˡ : (x : Seq A) → append empty x ≡ x
    --   idʳ : (x : Seq A) → append x empty ≡ x

    singleton : cmp (Π A λ _ → F (Seq A))
    empty : cmp (F (Seq A))
    append : cmp (Π (Seq A) λ _ → Π (Seq A) λ _ → F (Seq A))
    isMonoid : ◯ (A.IsMonoid (_≅_ {F (Seq A)}) (lift₂ {X = F (Seq A)} append) empty)

    singleton' : ◯ (val A → val (Seq A))
    singleton'/match : (u : ext) (a : val A) → singleton {A} a ≡ ret (singleton' u a)
    empty' : ◯ (val (Seq A))
    empty'/match : (u : ext) → empty {A} ≡ ret (empty' u)
    append' : ◯ (val (Seq A) → val (Seq A) → val (Seq A))
    append'/match : (u : ext) (s₁ s₂ : val (Seq A)) → append {A} s₁ s₂ ≡ ret (append' u s₁ s₂)

    mapreduce :
      {X : tp neg}
      → cmp (Π A λ _ → X)
      → (z : cmp X)
      → (g : cmp (Π (U X) λ _ → Π (U X) λ _ → X))
      → ◯ (A.IsMonoid (_≅_ {X}) g z)
      → val (Seq A)
      → cmp X
    mapreduce/singleton : ∀ {f z g h a}     → ◯ (bind X (singleton {A} a ) (mapreduce {X = X} f z g h) ≡ f a)
    mapreduce/empty     : ∀ {f z g h}       → ◯ (bind X (empty {A}       ) (mapreduce {X = X} f z g h) ≡ z)
    mapreduce/append    : ∀ {f z g h s₁ s₂} → ◯ (bind X (append {A} s₁ s₂) (mapreduce {X = X} f z g h) ≡ g (mapreduce {X = X} f z g h s₁) (mapreduce {X = X} f z g h s₂))
    mapreduce/singleton' : ∀ {f z g h a}     → (u : ext) → mapreduce {X = X} f z g h (singleton' {A} u a ) ≡ f a
    mapreduce/empty'     : ∀ {f z g h}       → (u : ext) → mapreduce {X = X} f z g h (empty' {A} u       ) ≡ z
    mapreduce/append'    : ∀ {f z g h s₁ s₂} → (u : ext) → mapreduce {X = X} f z g h (append' {A} u s₁ s₂) ≡ g (mapreduce {X = X} f z g h s₁) (mapreduce {X = X} f z g h s₂)
    mapreduce/singleton'' : ∀ {f z g h a}     → ◯ (cmp (tbind (singleton {A} a ) (λ s → meta (mapreduce {X = X} f z g h s ≡ f a))))
    mapreduce/empty''     : ∀ {f z g h}       → ◯ (cmp (tbind (empty {A}       ) (λ s → meta (mapreduce {X = X} f z g h s ≡ z))))
    mapreduce/append''    : ∀ {f z g h s₁ s₂} → ◯ (cmp (tbind (append {A} s₁ s₂) (λ s → meta (mapreduce {X = X} f z g h s ≡ g (mapreduce {X = X} f z g h s₁) (mapreduce {X = X} f z g h s₂)))))

    induction :
      {P : val (Seq A) → tp neg}
      → cmp (Π A λ a → tbind (singleton a) P)
      → (z : cmp (tbind empty P))
      → (g : cmp (Π (Seq A) λ s₁ → Π (Seq A) λ s₂ → Π (U (P s₁)) λ _ → Π (U (P s₂)) λ _ → tbind (append s₁ s₂) P))
      → ◯ (A.IsMonoid (_≅_ {{!   !}}) {!   !} {!   !})
      → (s : val (Seq A))
      → cmp (P s)
    induction/singleton : ∀ {P f z g h a}     → ◯ (dbind P (singleton {A} a ) (induction {P = P} f z g h) ≡ f a)
    induction/empty     : ∀ {P f z g h}       → ◯ (dbind P (empty {A}       ) (induction {P = P} f z g h) ≡ z)
    induction/append    : ∀ {P f z g h s₁ s₂} → ◯ (dbind P (append {A} s₁ s₂) (induction {P = P} f z g h) ≡ g s₁ s₂ (induction {P = P} f z g h s₁) (induction {P = P} f z g h s₂))

module Example (S : SEQUENCE_CORE) where
  open SEQUENCE_CORE S

  id-traverse : cmp (Π (Seq A) λ s → F (Seq A))
  id-traverse {A = A} = mapreduce {X = F (Seq A)} singleton empty (lift₂ {X = F (Seq A)} append) (isMonoid S)

  example₀ : ◯ (id-traverse {A = A} ≡ ret)
  example₀ {A = A} u = funext λ s →
    let aux = (λ e → cmp (tbind e λ s → meta (id-traverse s ≡ ret s)))
        open ≡-Reasoning
    in
    induction
      {P = λ s → meta (id-traverse s ≡ ret s)}
      (λ a → Eq.subst aux (Eq.sym (singleton'/match u a))
        (begin
          id-traverse (singleton' u a)
        ≡⟨ mapreduce/singleton' u ⟩
          singleton a
        ≡⟨ singleton'/match u a ⟩
          ret (singleton' u a)
        ∎))
      (Eq.subst aux (Eq.sym (empty'/match u))
        (begin
          id-traverse (empty' u)
        ≡⟨ mapreduce/empty' u ⟩
          empty
        ≡⟨ empty'/match u ⟩
          ret (empty' u)
        ∎))
      (λ s₁ s₂ ih₁ ih₂ → Eq.subst aux (Eq.sym (append'/match u s₁ s₂))
        (begin
          id-traverse (append' u s₁ s₂)
        ≡⟨ mapreduce/append' u ⟩
          lift₂ {X = F (Seq A)} append (id-traverse s₁) (id-traverse s₂)
        ≡⟨ Eq.cong₂ (lift₂ {X = F (Seq A)} append) ih₁ ih₂ ⟩
          lift₂ {X = F (Seq A)} append (ret {Seq A} s₁) (ret {Seq A} s₂)
        ≡⟨ append'/match u s₁ s₂ ⟩
          ret (append' u s₁ s₂)
        ∎))
      {!   !}
      s

  map : cmp (Π (U (Π A λ _ → F B)) λ _ → Π (Seq A) λ _ → F (Seq B))
  map {B = B} f =
    mapreduce {X = F (Seq B)}
      (lift₁ {X = F (Seq B)} singleton ∘ f)
      empty
      (lift₂ {X = F (Seq B)} append)
      (isMonoid S)

  sum : cmp (Π (Seq nat) λ _ → F nat)
  sum =
    mapreduce {X = F nat}
      ret
      (ret 0)
      (lift₂ {X = F nat} λ n₁ n₂ → ret (n₁ + n₂))
      {!   !}

  reverse : cmp (Π (Seq A) λ _ → F (Seq A))
  reverse {A = A} =
    mapreduce {X = F (Seq A)}
      singleton
      empty
      (λ s₁ s₂ → lift₂ {X = F (Seq A)} append s₂ s₁)
      {!   !}

  example₁ : (f : cmp (Π A λ _ → F B)) (s : val (Seq A)) → lift₁ {X = F (Seq B)} (map f) (reverse s) ≡ lift₁ {X = F (Seq B)} reverse (map f s)
  example₁ = {!   !}

  example₂ : (s : val (Seq nat)) → bind (F nat) (reverse s) sum ≡ sum s
  example₂ = {!   !}
