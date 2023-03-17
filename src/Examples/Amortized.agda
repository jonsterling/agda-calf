{-# OPTIONS --prop --rewriting --guardedness --lossy-unification #-}

module Examples.Amortized where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
-- open CostMonoid costMonoid

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
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_)
open import Data.Bool as Bool using (not; _∧_)
open import Data.Product
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


-- record DynamicArray (A : tp pos) : Set where
--   coinductive
--   field
--     append : cmp (Π A λ _ → meta (DynamicArray A))
--     deq : cmp (Π )


record Queue (A : tp pos) : Set where
  coinductive
  constructor ⟪_,_⟫
  field
    enq : cmp (Π A λ _ → meta (Queue A))
    deq : cmp (F (prod⁺ (maybe A) (U (meta (Queue A)))))
queue : tp pos → tp neg
queue A = meta (Queue A)

postulate
  mylaw : ∀ {c e₁ e₂} → step (queue A) c ⟪ e₁ , e₂ ⟫ ≡ ⟪ step (Π A λ _ → queue A) c e₁ , step _ c e₂ ⟫
{-# REWRITE mylaw #-}

{-# TERMINATING #-}
l-queue : cmp (Π (list A) λ _ → queue A)
Queue.enq (l-queue {A} l) x = step (queue A) (length l) (l-queue (l ++ [ x ]))
Queue.deq (l-queue {A} []) = ret (nothing , l-queue [])
Queue.deq (l-queue {A} (x ∷ l)) = ret (just x , l-queue l)

{-# TERMINATING #-}
ll-queue : cmp (Π (list A) λ _ → Π (list A) λ _ → queue A)
Queue.enq (ll-queue {A} bl fl) x = ll-queue (x ∷ bl) fl
Queue.deq (ll-queue {A} bl []) with reverse bl
... | [] = ret (nothing , ll-queue [] [])
... | x ∷ fl = step _ (length bl) (ret (just x , ll-queue [] fl))
Queue.deq (ll-queue {A} bl (x ∷ fl)) = ret (just x , ll-queue bl fl)

{-# TERMINATING #-}
ll-queue' : cmp (Π (list A) λ _ → Π (list A) λ _ → queue A)
Queue.enq (ll-queue' {A} bl fl) x = step (queue A) 1 (ll-queue' (x ∷ bl) fl)
Queue.deq (ll-queue' {A} bl []) with reverse bl
... | [] = ret (nothing , ll-queue' [] [])
... | x ∷ fl = ret (just x , ll-queue' [] fl)
Queue.deq (ll-queue' {A} bl (x ∷ fl)) = ret (just x , ll-queue' bl fl)


ex : cmp (queue nat)
ex = ll-queue (5 ∷ 4 ∷ 3 ∷ []) (1 ∷ 2 ∷ [])


record Queue/cost (A : tp pos) : Set where
  coinductive
  constructor ⟪_,_⟫
  field
    enq : cmp (Π A λ _ → meta (Queue/cost A))
    deq : cmp cost × Queue/cost A
queue/cost : tp pos → tp neg
queue/cost A = meta (Queue/cost A)

ll-queue/cost : cmp (Π (list A) λ _ → Π (list A) λ _ → queue/cost A)
Queue/cost.enq (ll-queue/cost bl fl) x = ll-queue/cost (x ∷ bl) fl
Queue/cost.deq (ll-queue/cost bl []) with reverse bl
... | [] = 0 , ll-queue/cost [] []
... | x ∷ fl = length bl , ll-queue/cost [] fl
Queue/cost.deq (ll-queue/cost bl (x ∷ fl)) = 0 , ll-queue/cost bl fl

record Queue/hascost {A : tp pos} (e : Queue A) (c : Queue/cost A) : Set where
  coinductive
  constructor ⟪_,_⟫
  field
    enq : (a : val A) → Queue/hascost (Queue.enq e a) (Queue/cost.enq c a)
    deq : Σ (val (maybe A)) λ v → Σ (cmp (queue A)) λ q' → (Queue.deq e ≡ step _ (proj₁ (Queue/cost.deq c)) (ret (v , q'))) × Queue/hascost q' (proj₂ (Queue/cost.deq c))

ll-queue/hascost : (bl fl : val (list A)) → Queue/hascost (ll-queue bl fl) (ll-queue/cost bl fl)
Queue/hascost.enq (ll-queue/hascost bl fl) x = ll-queue/hascost (x ∷ bl) fl
Queue/hascost.deq (ll-queue/hascost bl []) = {!   !}
Queue/hascost.deq (ll-queue/hascost bl (x ∷ fl)) = just x , ll-queue bl fl , refl , ll-queue/hascost bl fl

ll-queue/cost/closed : cmp (Π nat λ _ → queue/cost A)
Queue/cost.enq (ll-queue/cost/closed n) x = ll-queue/cost/closed (suc n)
Queue/cost.deq (ll-queue/cost/closed n)  = n , ll-queue/cost/closed zero

record _q≤_ {A : tp pos} (c₁ : Queue/cost A) (c₂ : Queue/cost A) : Set where
  coinductive
  constructor ⟪_,_⟫
  field
    enq : (a : val A) → (Queue/cost.enq c₁ a) q≤ (Queue/cost.enq c₂ a)
    deq : (proj₁ (Queue/cost.deq c₁) Nat.≤ proj₁ (Queue/cost.deq c₂)) × (proj₂ (Queue/cost.deq c₁) q≤ proj₂ (Queue/cost.deq c₂))

demo : (bl : val (list A)) → ll-queue/cost bl [] q≤ ll-queue/cost/closed (length bl)
_q≤_.enq (demo bl) x = demo (x ∷ bl)
_q≤_.deq (demo bl) = {!   !} , {!   !}



record Simple : Set where
  coinductive
  constructor ⦅_,_⦆
  field
    poke : cmp (F unit)
    next : cmp (meta Simple)
simple : tp neg
simple = meta (Simple)

postulate
  simple/law : {c : cmp cost} {e₁ : cmp (F unit)} {e₂ : cmp simple} →
    step simple c ⦅ e₁ , e₂ ⦆ ≡ ⦅ step (F unit) c e₁ , step simple c e₂ ⦆
  simple/law' : {c : cmp cost} {e : cmp simple} → Simple.poke (step simple c e) ≡ step (F unit) c (Simple.poke e)
  simple/law'' : {c : cmp cost} {e : cmp simple} → Simple.next (step simple c e) ≡ step simple c (Simple.next e)
{-# REWRITE simple/law simple/law' simple/law'' #-}

{-# TERMINATING #-}
simple₁ : cmp simple
Simple.poke simple₁ = step (F unit) 1 (ret triv)
Simple.next simple₁ = step simple 1 simple₁

{-# TERMINATING #-}
simple₂ : cmp (Π bool λ _ → simple)
Simple.poke (simple₂ false) = step (F unit) 1 (ret triv)
Simple.next (simple₂ false) = step simple 2 (simple₂ true)
Simple.poke (simple₂ true) = ret triv
Simple.next (simple₂ true) = simple₂ false

record _s≈_ (s₁ s₂ : cmp simple) : Set where
  coinductive
  constructor ⦅_⦆
  field
    poke : Simple.poke s₁ ≡ Simple.poke s₂
    next : Simple.next s₁ s≈ Simple.next s₂

cong : (f : Simple → Simple) {x y : Simple} → x s≈ y → f x s≈ f y
_s≈_.poke (cong f h) = Eq.cong (Simple.poke ∘ f) {!   !}
_s≈_.next (cong f h) = cong (Simple.next ∘ f) h

{-# TERMINATING #-}
foo/false : simple₁ s≈ simple₂ false
foo/true  : simple₁ s≈ step simple 1 (simple₂ true)
_s≈_.poke foo/false = refl
_s≈_.next foo/false = cong (step simple 1) foo/true
_s≈_.poke foo/true = refl
_s≈_.next foo/true = cong (step simple 1) foo/false

record Simple/cost : Set where
  coinductive
  constructor ⦅_⦆
  field
    poke : cmp cost × Simple/cost
simple/cost : tp neg
simple/cost = meta Simple/cost

simple₁/cost : cmp simple/cost
Simple/cost.poke simple₁/cost = 1 , simple₁/cost

simple₂/cost : cmp (Π bool λ _ → simple/cost)
Simple/cost.poke (simple₂/cost false) = 2 , simple₂/cost true
Simple/cost.poke (simple₂/cost true) = 0 , simple₂/cost false

record _s≤_ (c₁ : Simple/cost) (c₂ : Simple/cost) : Set where
  coinductive
  constructor ⦅_⦆
  field
    poke : (proj₁ (Simple/cost.poke c₁) Nat.≤ proj₁ (Simple/cost.poke c₂)) × (proj₂ (Simple/cost.poke c₁) s≤ proj₂ (Simple/cost.poke c₂))

simple₁/cost≤simple₂/cost : simple₁/cost s≤ simple₂/cost false
_s≤_.poke simple₁/cost≤simple₂/cost = {!   !} , {!   !}
