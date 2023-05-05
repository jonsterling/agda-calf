{-# OPTIONS --prop --rewriting #-}

module Examples.SequenceNew where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Unit
open import Calf.Types.Bool
open import Calf.Types.Sum using (inj₁; inj₂) renaming (sum to _⊎_)
open import Calf.Types.Eq
open import Calf.Types.Nat
open import Calf.Types.List as List using (list; []; _∷_; [_]; _++_)
open import Data.Nat as N using (_+_)
open import Data.Nat.Properties as N
open import Calf.Types.Bounded costMonoid

open import Function hiding (seq)

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)


variable
  A B C : tp pos
  X Y Z : tp neg
  P Q : val A → tp neg


record SEQUENCE_CORE : Set where
  field
    seq : tp pos → tp pos

    singleton : cmp (Π A λ _ → F (seq A))
    empty : cmp (F (seq A))
    append : cmp (Π (seq A) λ _ → Π (seq A) λ _ → F (seq A))

    mapreduce :
      {X : tp neg}
      → (f : cmp (Π A λ _ → X))
      → (z : cmp X)
      → (g : cmp (Π (U X) λ _ → Π (U X) λ _ → X))
      → val (seq A)
      → cmp X

ListSequence : SEQUENCE_CORE
ListSequence = record
  { seq = list
  ; singleton = λ a → ret [ a ]
  ; empty = ret []
  ; append = λ {A} s₁ s₂ → step (F (list A)) (List.length s₁ + List.length s₂ , 1) (ret (s₁ ++ s₂))
  ; mapreduce = λ {A} {X} → mapreduce {A} {X}
  }
  where
    mapreduce :
      {X : tp neg}
      → (f : cmp (Π A λ _ → X))
      → (z : cmp X)
      → (g : cmp (Π (U X) λ _ → Π (U X) λ _ → X))
      → val (list A)
      → cmp X
    mapreduce f z g []      = z
    mapreduce {A} {X} f z g (x ∷ l) = g (f x) (mapreduce {A} {X} f z g l)

ArraySequence : SEQUENCE_CORE
ArraySequence = {!   !}

TreeSequence : SEQUENCE_CORE
TreeSequence = {!   !}

module Examples (Sequence : SEQUENCE_CORE) where
  open SEQUENCE_CORE Sequence public

  -- val nth : 'a seq -> int -> 'a option

  -- val length : 'a seq -> int
  length : cmp (Π (seq A) λ _ → F nat)
  length =
    mapreduce {X = F nat}
      (λ _ → ret 1)
      (ret 0)
      (λ ih₁ ih₂ →
        bind (F nat) (ih₁ & ih₂) λ (n₁ , n₂) →
        ret (n₁ + n₂))

  -- val equal : ('a * 'a -> bool) -> 'a seq * 'a seq -> bool
  -- val tabulate : (int -> 'a) -> int -> 'a seq
  -- val rev : 'a seq -> 'a seq
  -- val flatten : 'a seq seq -> 'a seq
  -- val filter : ('a -> bool) -> 'a seq -> 'a seq
  -- val map : ('a -> 'b) -> 'a seq -> 'b seq
  -- val zip : 'a seq * 'b seq -> ('a * 'b) seq
  -- val reduce : ('a * 'a -> 'a) -> 'a -> 'a seq -> 'a
  -- val scan : ('a * 'a -> 'a) -> 'a -> 'a seq -> 'a seq * 'a

module Test where
  open Examples ListSequence

  ex =
    bind (F nat) (singleton {bool} true) λ s →
    length {bool} s

  -- hit Ctrl-c Ctrl-n
  compute = {! ex  !}
