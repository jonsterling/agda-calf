{-# OPTIONS --prop --rewriting --guardedness #-}

module Examples.Amortized where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Level using (0ℓ)

open import Calf costMonoid
open import Calf.Types.Unit
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Bool
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.Bounded costMonoid
open import Data.String using (String)
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_; _^_; _∸_; pred)
open import Data.Bool as Bool using (not; _∧_)
open import Data.Product
import Data.Nat as Nat
import Data.Nat.Properties as Nat
open import Data.Nat.PredExp2
import Data.List as List
import Data.List.Properties as List
import Data.Fin as Fin
open import Data.Vec as Vec using (Vec)

open import Function

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)

variable
  A B C : tp pos
  X Y Z : tp neg
  P Q : val A → tp neg


record Queue (A : tp pos) : Set where
  coinductive
  field
    enq : cmp (Π A λ _ → meta (Queue A))
    deq : cmp (F (prod⁺ (maybe A) (U (meta (Queue A)))))
    quit : cmp (F unit)
queue : tp pos → tp neg
queue A = meta (Queue A)

postulate
  queue/law/enq : ∀ {c e} → Queue.enq (step (queue A) c e) ≡ step (Π A λ _ → queue A) c (Queue.enq e)
  queue/law/deq : ∀ {c e} → Queue.deq (step (queue A) c e) ≡ step (F (prod⁺ (maybe A) (U (meta (Queue A))))) c (Queue.deq e)
  queue/law/quit : ∀ {c e} → Queue.quit (step (queue A) c e) ≡ step (F unit) c (Queue.quit e)
{-# REWRITE queue/law/enq queue/law/deq queue/law/quit #-}

{-# TERMINATING #-}
l-queue : cmp (Π (list A) λ _ → queue A)
Queue.enq (l-queue {A} l) a = step (queue A) (length l) (l-queue (l ++ [ a ]))
Queue.deq (l-queue {A} []) = ret (nothing , l-queue [])
Queue.deq (l-queue {A} (a ∷ l)) = ret (just a , l-queue l)
Queue.quit (l-queue {A} l) = ret triv

{-# TERMINATING #-}
ll-queue : cmp (Π (list A) λ _ → Π (list A) λ _ → queue A)
Queue.enq (ll-queue {A} bl fl) a = ll-queue (a ∷ bl) fl
Queue.deq (ll-queue {A} bl []) with reverse bl
... | [] = ret (nothing , ll-queue [] [])
... | a ∷ fl = step (F (prod⁺ (maybe A) (U (meta (Queue A))))) (length bl) (ret (just a , ll-queue [] fl))
Queue.deq (ll-queue {A} bl (a ∷ fl)) = ret (just a , ll-queue bl fl)
Queue.quit (ll-queue {A} bl fl) = step (F unit) (length bl) (ret triv)
  -- (length bl) is the remaining potential; get rid of it

{-# TERMINATING #-}
ll-queue' : cmp (Π (list A) λ _ → Π (list A) λ _ → queue A)
Queue.enq (ll-queue' {A} bl fl) a = step (queue A) 1 (ll-queue' (a ∷ bl) fl)
Queue.deq (ll-queue' {A} bl []) with reverse bl
... | [] = ret (nothing , ll-queue' [] [])
... | a ∷ fl = ret (just a , ll-queue' [] fl)
Queue.deq (ll-queue' {A} bl (a ∷ fl)) = ret (just a , ll-queue' bl fl)
Queue.quit (ll-queue' {A} bl fl) = ret triv


{-# NO_POSITIVITY_CHECK #-}
record _q≈_ {A : tp pos} (q₁ q₂ : cmp (queue A)) : Set where
  coinductive
  field
    enq : cmp (Π A λ a → meta (Queue.enq q₁ a q≈ Queue.enq q₂ a))
    deq :
      Σ ℂ λ c₁ → Σ (val (maybe A)) λ a₁ → Σ (cmp (queue A)) λ q₁' → Queue.deq q₁ ≡ step (F (prod⁺ (maybe A) (U (meta (Queue A))))) c₁ (ret (a₁ , q₁')) ×
      Σ ℂ λ c₂ → Σ (val (maybe A)) λ a₂ → Σ (cmp (queue A)) λ q₂' → Queue.deq q₂ ≡ step (F (prod⁺ (maybe A) (U (meta (Queue A))))) c₂ (ret (a₂ , q₂')) ×
      -- (c₁ ≡ c₂) ×  -- not amortized
      (a₁ ≡ a₂) ×
      -- (q₁' q≈ q₂')  -- not amortized
      (step (queue A) c₁ q₁' q≈ step (queue A) c₂ q₂')  -- amortized

      -- cmp
      --   ( tbind (Queue.deq q₁) λ (a₁ , q₁') →
      --     tbind (Queue.deq q₂) λ (a₂ , q₂') →
      --     F (prod⁺ (eq (maybe A) a₁ a₂) (U (meta (q₁' q≈ q₂'))))
      --   )
    quit : Queue.quit q₁ ≡ Queue.quit q₂

q-cong : (c : cmp cost) {x y : Queue A} → x q≈ y → step (queue A) c x q≈ step (queue A) c y
_q≈_.enq (q-cong c {x} {y} h) a = q-cong c (_q≈_.enq h a)
_q≈_.deq (q-cong {A} c h) =
  let (c₁ , a₁ , q₁' , h₁ , c₂ , a₂ , q₂' , h₂ , ha , hq') = _q≈_.deq h in
  c + c₁ , a₁ , q₁' , Eq.cong (step (F (prod⁺ (maybe A) (U (queue A)))) c) h₁ ,
  c + c₂ , a₂ , q₂' , Eq.cong (step (F (prod⁺ (maybe A) (U (queue A)))) c) h₂ ,
  ha , q-cong c hq'
_q≈_.quit (q-cong c h) = Eq.cong (step (F unit) c) (_q≈_.quit h)

{-# TERMINATING #-}
ll-queue/q≈ : (bl fl : val (list A)) →
  ll-queue bl fl q≈ step (queue A) (length bl) (ll-queue' bl fl)
  -- (length bl) is the initial potential to ask for
_q≈_.enq (ll-queue/q≈ {A} bl fl) a rewrite Nat.+-comm (length bl) 1 = ll-queue/q≈ (a ∷ bl) fl
_q≈_.deq (ll-queue/q≈ {A} bl []) with reverse bl | lemma bl
  where
    lemma : (l : val (list A)) → reverse l ≡ [] → l ≡ []
    lemma [] refl = refl
    lemma (x ∷ l) h with reverse (x ∷ l) | List.length-reverse (x ∷ l)
    lemma (x ∷ l) refl | .[] | ()
... | [] | h rewrite h refl =
        zero , nothing , ll-queue [] [] , refl ,
        zero , nothing , ll-queue' [] [] , refl ,
        refl , ll-queue/q≈ [] []
... | a ∷ fl | _ =
        length bl , just a , ll-queue [] fl , refl ,
        length bl , just a , ll-queue' [] fl , refl ,
        refl , q-cong (length bl) (ll-queue/q≈ [] fl)
_q≈_.deq (ll-queue/q≈ {A} bl (a ∷ fl)) =
  zero , just a , ll-queue bl fl , refl ,
  length bl , just a , ll-queue' bl fl , refl ,
  refl , ll-queue/q≈ bl fl
_q≈_.quit (ll-queue/q≈ {A} bl fl) = refl


-- {-# TERMINATING #-}
-- fake-queue : cmp (queue A)
-- Queue.enq fake-queue a = fake-queue
-- Queue.deq fake-queue = ret (nothing , fake-queue)
-- Queue.quit fake-queue = ret triv

-- issue : (c₁ c₂ : ℂ) → step (queue A) c₁ fake-queue q≈ step (queue A) c₂ fake-queue
-- _q≈_.enq (issue c₁ c₂) a = issue c₁ c₂
-- _q≈_.deq (issue c₁ c₂) =
--   c₁ , nothing , fake-queue , refl ,
--   c₂ , nothing , fake-queue , refl ,
--   refl , issue c₁ c₂
-- _q≈_.quit (issue c₁ c₂) = {!   !}


--------------------------------------------------------------------------------


record DynamicArray (A : tp pos) : Set where
  coinductive
  field
    append : cmp (Π A λ _ → meta (DynamicArray A))
    get : cmp (Π nat λ _ → F (prod⁺ (maybe A) (U (meta (DynamicArray A)))))
    quit : cmp (F unit)
dynamic-array : tp pos → tp neg
dynamic-array A = meta (DynamicArray A)

postulate
  dynamic-array/law/append : ∀ {c e} → DynamicArray.append (step (dynamic-array A) c e) ≡ step (Π A λ _ → dynamic-array A) c (DynamicArray.append e)
  dynamic-array/law/get : ∀ {c e} → DynamicArray.get (step (dynamic-array A) c e) ≡ step (Π nat λ _ → F (prod⁺ (maybe A) (U (meta (DynamicArray A))))) c (DynamicArray.get e)
  dynamic-array/law/quit : ∀ {c e} → DynamicArray.quit (step (dynamic-array A) c e) ≡ step (F unit) c (DynamicArray.quit e)
{-# REWRITE dynamic-array/law/append dynamic-array/law/get dynamic-array/law/quit #-}

-- vec : tp pos → val nat → tp pos
-- vec A n = U (meta (Vec (val A) n))

{-# TERMINATING #-}
-- dynarr₁ n m
-- length of allocated array: (2 ^ n)
-- remaining free spaces: m (≤ 2 ^ (pred n))
dynarr₁ : cmp (Π nat λ _ → Π nat λ _ → dynamic-array unit)
DynamicArray.append (dynarr₁ n zero) triv = step (dynamic-array unit) (2 ^ n) (dynarr₁ (suc n) pred[2^ n ])
DynamicArray.append (dynarr₁ n (suc m)) triv = dynarr₁ n m
DynamicArray.get (dynarr₁ n m) i with i Nat.<? 2 ^ n ∸ m
... | no ¬p = ret (nothing , dynarr₁ n m)
... | yes p = ret (just triv , dynarr₁ n m)
DynamicArray.quit (dynarr₁ n m) = step (F unit) (2 ^ n ∸ 2 * m) (ret triv)

{-# TERMINATING #-}
dynarr₂ : cmp (Π nat λ _ → dynamic-array unit)
DynamicArray.append (dynarr₂ n) triv = step (dynamic-array unit) 2 (dynarr₂ (suc n))
DynamicArray.get (dynarr₂ n) i with i Nat.<? n
... | no ¬p = ret (nothing , dynarr₂ n)
... | yes p = ret (just triv , dynarr₂ n)
DynamicArray.quit (dynarr₂ n) = ret triv

{-# NO_POSITIVITY_CHECK #-}
record _d≈_ {A : tp pos} (d₁ d₂ : cmp (dynamic-array A)) : Set where
  coinductive
  field
    append : cmp (Π A λ a → meta (DynamicArray.append d₁ a d≈ DynamicArray.append d₂ a))
    get :
      (i : val nat) →
        Σ ℂ λ c₁ → Σ (val (maybe A)) λ a₁ → Σ (cmp (dynamic-array A)) λ d₁' → DynamicArray.get d₁ i ≡ step (F (prod⁺ (maybe A) (U (meta (DynamicArray A))))) c₁ (ret (a₁ , d₁')) ×
        Σ ℂ λ c₂ → Σ (val (maybe A)) λ a₂ → Σ (cmp (dynamic-array A)) λ d₂' → DynamicArray.get d₂ i ≡ step (F (prod⁺ (maybe A) (U (meta (DynamicArray A))))) c₂ (ret (a₂ , d₂')) ×
        -- (c₁ ≡ c₂) ×  -- not amortized
        (a₁ ≡ a₂) ×
        -- (d₁' d≈ d₂')  -- not amortized
        (step (dynamic-array A) c₁ d₁' d≈ step (dynamic-array A) c₂ d₂')  -- amortized
    quit : DynamicArray.quit d₁ ≡ DynamicArray.quit d₂

d-cong : (c : cmp cost) {x y : DynamicArray A} → x d≈ y → step (dynamic-array A) c x d≈ step (dynamic-array A) c y
_d≈_.append (d-cong c h) a = d-cong c (_d≈_.append h a)
_d≈_.get (d-cong {A} c h) i =
  let (c₁ , a₁ , d₁' , h₁ , c₂ , a₂ , d₂' , h₂ , ha , hd') = _d≈_.get h i in
  c + c₁ , a₁ , d₁' , Eq.cong (step (F (prod⁺ (maybe A) (U (dynamic-array A)))) c) h₁ ,
  c + c₂ , a₂ , d₂' , Eq.cong (step (F (prod⁺ (maybe A) (U (dynamic-array A)))) c) h₂ ,
  ha , d-cong c hd'
_d≈_.quit (d-cong c h) = Eq.cong (step (F unit) c) (_d≈_.quit h)

-- from unreleased agda-stdlib
2^n>0 : ∀ (n : ℕ) → 2 ^ n > 0
2^n>0 zero = Nat.s≤s Nat.z≤n
2^n>0 (suc n) = Nat.≤-trans (2^n>0 n) (Nat.m≤m+n (2 ^ n) ((2 ^ n) + zero))

2^-mono : {m n : ℕ} → m Nat.≤ n → 2 ^ m Nat.≤ 2 ^ n
2^-mono {n = n} Nat.z≤n = 2^n>0 n
2^-mono (Nat.s≤s h) = Nat.*-monoʳ-≤ 2 (2^-mono h)

2^suc[pred[n]] : (n : ℕ) → 2 ^ suc (pred n) ∸ 2 Nat.≤ 2 ^ n
2^suc[pred[n]] zero = Nat.z≤n
2^suc[pred[n]] (suc n) = Nat.m∸n≤m (2 ^ suc n) 2

{-# TERMINATING #-}
dynarr/d≈ : (n m : val nat) → m Nat.≤ pred[2^ pred n ] →
  dynarr₁ n m d≈ step (dynamic-array unit) (2 ^ n ∸ 2 * m) (dynarr₂ (2 ^ n ∸ m))
_d≈_.append (dynarr/d≈ n zero h) triv =
  Eq.subst₂
    (λ c x →
      step (dynamic-array unit) (2 ^ n) (dynarr₁ (suc n) (2 ^ n ∸ 1)) d≈
      step (dynamic-array unit) (2 ^ n + c) (dynarr₂ x))
    {x = 2 ^ suc n ∸ 2 * pred[2^ n ]}
    {y = 2}
    {u = 2 ^ suc n ∸ pred[2^ n ]}
    {v = suc (2 ^ n)}
    (let open ≡-Reasoning in
    begin
      2 ^ suc n ∸ 2 * pred[2^ n ]
    ≡⟨ Eq.cong (2 ^ suc n ∸_) (Nat.*-distribˡ-∸ 2 (2 ^ n) 1) ⟩
      2 ^ suc n ∸ (2 * 2 ^ n ∸ 2)
    ≡⟨⟩
      2 ^ suc n ∸ (2 ^ suc n ∸ 2)
    ≡⟨ Nat.m∸[m∸n]≡n (Nat.*-monoʳ-≤ 2 (2^n>0 n)) ⟩
      2
    ∎)
    (let open ≡-Reasoning in
    begin
      2 ^ suc n ∸ pred[2^ n ]
    ≡⟨⟩
      2 * 2 ^ n ∸ (2 ^ n ∸ 1)
    ≡⟨⟩
      (2 ^ n + (2 ^ n + 0)) ∸ (2 ^ n ∸ 1)
    ≡⟨ Eq.cong (λ x → (2 ^ n) + x ∸ (2 ^ n ∸ 1)) (Nat.+-identityʳ (2 ^ n)) ⟩
      (2 ^ n + 2 ^ n) ∸ (2 ^ n ∸ 1)
    ≡⟨ Nat.+-∸-assoc (2 ^ n) {n = 2 ^ n} {o = 2 ^ n ∸ 1} (Nat.m∸n≤m (2 ^ n) 1) ⟩
      2 ^ n + (2 ^ n ∸ (2 ^ n ∸ 1))
    ≡⟨ Eq.cong (2 ^ n +_) (Nat.m∸[m∸n]≡n (2^n>0 n)) ⟩
      2 ^ n + 1
    ≡⟨ Nat.+-comm (2 ^ n) 1 ⟩
      suc (2 ^ n)
    ∎)
    (d-cong (2 ^ n)
      {x = dynarr₁ (suc n) pred[2^ n ]}
      {y = step (dynamic-array unit) (2 ^ suc n ∸ 2 * pred[2^ n ]) (dynarr₂ (2 ^ suc n ∸ pred[2^ n ]))}
      (dynarr/d≈ (suc n) pred[2^ n ] Nat.≤-refl))
_d≈_.append (dynarr/d≈ n (suc m) h) triv =
  Eq.subst₂
    (λ c x → dynarr₁ n m d≈ step (dynamic-array unit) c (dynarr₂ x))
    {x = 2 ^ n ∸ 2 * m}
    {y = 2 ^ n ∸ 2 * suc m + 2}
    {u = 2 ^ n ∸ m}
    {v = suc (2 ^ n ∸ suc m)}
    (let
      lemma : suc (suc (m + (m + zero))) Nat.≤ (2 ^ n)
      lemma =
        let open Nat.≤-Reasoning in
        begin
          suc (suc (m + (m + zero)))
        ≡˘⟨ Eq.cong suc (Nat.+-suc m (m + zero)) ⟩
          suc m + (suc m + zero)
        ≤⟨ Nat.+-mono-≤ h (Nat.+-monoˡ-≤ zero h) ⟩
          pred[2^ pred n ] + (pred[2^ pred n ] + zero)
        ≡⟨ Nat.*-distribˡ-∸ 2 (2 ^ pred n) 1 ⟩
          2 ^ suc (pred n) ∸ 2
        ≤⟨ 2^suc[pred[n]] n ⟩
          2 ^ n
        ∎
    in
    let open ≡-Reasoning in
    begin
      2 ^ n ∸ 2 * m
    ≡˘⟨ Nat.[m+n]∸[m+o]≡n∸o 2 (2 ^ n) (2 * m) ⟩
      (2 + 2 ^ n) ∸ (2 + 2 * m)
    ≡⟨ Nat.+-∸-assoc 2 {n = 2 ^ n} {o = 2 + 2 * m} lemma ⟩
      2 + (2 ^ n ∸ (2 + 2 * m))
    ≡⟨ Nat.+-comm 2 (2 ^ n ∸ (2 + 2 * m)) ⟩
      2 ^ n ∸ (2 + 2 * m) + 2
    ≡˘⟨ Eq.cong (λ x → 2 ^ n ∸ x + 2) (Nat.*-distribˡ-+ 2 1 m) ⟩
      2 ^ n ∸ 2 * suc m + 2
    ∎)
    (let open ≡-Reasoning in
    begin
      2 ^ n ∸ m
    ≡˘⟨ Nat.[m+n]∸[m+o]≡n∸o 1 (2 ^ n) m ⟩
      suc (2 ^ n) ∸ suc m
    ≡⟨
      Nat.+-∸-assoc
        1
        (Nat.≤-trans h (Nat.∸-mono (2^-mono {n = n} Nat.pred[n]≤n) (Nat.z≤n {1})))
    ⟩
      suc (2 ^ n ∸ suc m)
    ∎)
    (dynarr/d≈ n m (Nat.<⇒≤ h))
_d≈_.get (dynarr/d≈ n m h) i with i Nat.<? 2 ^ n ∸ m
... | no ¬p =
        zero , nothing , dynarr₁ n m , refl ,
        2 ^ n ∸ 2 * m , nothing , dynarr₂ (2 ^ n ∸ m) , refl ,
        refl , dynarr/d≈ n m h
... | yes p =
        zero , just triv , dynarr₁ n m , refl ,
        2 ^ n ∸ 2 * m , just triv , dynarr₂ (2 ^ n ∸ m) , refl ,
        refl , dynarr/d≈ n m h
_d≈_.quit (dynarr/d≈ n m h) = refl

--------------------------------------------------------------------------------


-- record Queue/cost (A : tp pos) : Set where
--   coinductive
--   constructor ⟪_,_⟫
--   field
--     enq : cmp (Π A λ _ → meta (Queue/cost A))
--     deq : cmp cost × Queue/cost A
-- queue/cost : tp pos → tp neg
-- queue/cost A = meta (Queue/cost A)

-- ll-queue/cost : cmp (Π (list A) λ _ → Π (list A) λ _ → queue/cost A)
-- Queue/cost.enq (ll-queue/cost bl fl) a = ll-queue/cost (a ∷ bl) fl
-- Queue/cost.deq (ll-queue/cost bl []) with reverse bl
-- ... | [] = 0 , ll-queue/cost [] []
-- ... | a ∷ fl = length bl , ll-queue/cost [] fl
-- Queue/cost.deq (ll-queue/cost bl (a ∷ fl)) = 0 , ll-queue/cost bl fl

-- record Queue/hascost {A : tp pos} (e : Queue A) (c : Queue/cost A) : Set where
--   coinductive
--   constructor ⟪_,_⟫
--   field
--     enq : (a : val A) → Queue/hascost (Queue.enq e a) (Queue/cost.enq c a)
--     deq : Σ (val (maybe A)) λ v → Σ (cmp (queue A)) λ q' → (Queue.deq e ≡ step _ (proj₁ (Queue/cost.deq c)) (ret (v , q'))) × Queue/hascost q' (proj₂ (Queue/cost.deq c))

-- ll-queue/hascost : (bl fl : val (list A)) → Queue/hascost (ll-queue bl fl) (ll-queue/cost bl fl)
-- Queue/hascost.enq (ll-queue/hascost bl fl) a = ll-queue/hascost (a ∷ bl) fl
-- Queue/hascost.deq (ll-queue/hascost bl []) = {!   !}
-- Queue/hascost.deq (ll-queue/hascost bl (a ∷ fl)) = just a , ll-queue bl fl , refl , ll-queue/hascost bl fl

-- ll-queue/cost/closed : cmp (Π nat λ _ → queue/cost A)
-- Queue/cost.enq (ll-queue/cost/closed n) a = ll-queue/cost/closed (suc n)
-- Queue/cost.deq (ll-queue/cost/closed n)  = n , ll-queue/cost/closed zero

-- record _q≤_ {A : tp pos} (c₁ : Queue/cost A) (c₂ : Queue/cost A) : Set where
--   coinductive
--   constructor ⟪_,_⟫
--   field
--     enq : (a : val A) → (Queue/cost.enq c₁ a) q≤ (Queue/cost.enq c₂ a)
--     deq : (proj₁ (Queue/cost.deq c₁) Nat.≤ proj₁ (Queue/cost.deq c₂)) × (proj₂ (Queue/cost.deq c₁) q≤ proj₂ (Queue/cost.deq c₂))

-- demo : (bl : val (list A)) → ll-queue/cost bl [] q≤ ll-queue/cost/closed (length bl)
-- _q≤_.enq (demo bl) a = demo (a ∷ bl)
-- _q≤_.deq (demo bl) = {!   !} , {!   !}



-- record Simple : Set where
--   coinductive
--   constructor ⦅_,_⦆
--   field
--     poke : cmp (F unit)
--     next : cmp (meta Simple)
-- simple : tp neg
-- simple = meta (Simple)

-- postulate
--   simple/law : {c : cmp cost} {e₁ : cmp (F unit)} {e₂ : cmp simple} →
--     step simple c ⦅ e₁ , e₂ ⦆ ≡ ⦅ step (F unit) c e₁ , step simple c e₂ ⦆
--   simple/law' : {c : cmp cost} {e : cmp simple} → Simple.poke (step simple c e) ≡ step (F unit) c (Simple.poke e)
--   simple/law'' : {c : cmp cost} {e : cmp simple} → Simple.next (step simple c e) ≡ step simple c (Simple.next e)
-- {-# REWRITE simple/law simple/law' simple/law'' #-}

-- {-# TERMINATING #-}
-- simple₁ : cmp simple
-- Simple.poke simple₁ = step (F unit) 1 (ret triv)
-- Simple.next simple₁ = step simple 1 simple₁

-- {-# TERMINATING #-}
-- simple₂ : cmp (Π bool λ _ → simple)
-- Simple.poke (simple₂ false) = step (F unit) 1 (ret triv)
-- Simple.next (simple₂ false) = step simple 2 (simple₂ true)
-- Simple.poke (simple₂ true) = ret triv
-- Simple.next (simple₂ true) = simple₂ false

-- record _s≈_ (s₁ s₂ : cmp simple) : Set where
--   coinductive
--   constructor ⦅_⦆
--   field
--     poke : Simple.poke s₁ ≡ Simple.poke s₂
--     next : Simple.next s₁ s≈ Simple.next s₂

-- s≈-cong : (f : Simple → Simple) {x y : Simple} → x s≈ y → f x s≈ f y
-- _s≈_.poke (s≈-cong f h) = Eq.cong (Simple.poke ∘ f) {!   !}
-- _s≈_.next (s≈-cong f h) = s≈-cong (Simple.next ∘ f) h

-- {-# TERMINATING #-}
-- foo/false : simple₁ s≈ simple₂ false
-- foo/true  : simple₁ s≈ step simple 1 (simple₂ true)
-- _s≈_.poke foo/false = refl
-- _s≈_.next foo/false = s≈-cong (step simple 1) foo/true
-- _s≈_.poke foo/true = refl
-- _s≈_.next foo/true = s≈-cong (step simple 1) foo/false

-- record Simple/cost : Set where
--   coinductive
--   constructor ⦅_⦆
--   field
--     poke : cmp cost × Simple/cost
-- simple/cost : tp neg
-- simple/cost = meta Simple/cost

-- simple₁/cost : cmp simple/cost
-- Simple/cost.poke simple₁/cost = 1 , simple₁/cost

-- simple₂/cost : cmp (Π bool λ _ → simple/cost)
-- Simple/cost.poke (simple₂/cost false) = 2 , simple₂/cost true
-- Simple/cost.poke (simple₂/cost true) = 0 , simple₂/cost false

-- record _s≤_ (c₁ : Simple/cost) (c₂ : Simple/cost) : Set where
--   coinductive
--   constructor ⦅_⦆
--   field
--     poke : (proj₁ (Simple/cost.poke c₁) Nat.≤ proj₁ (Simple/cost.poke c₂)) × (proj₂ (Simple/cost.poke c₁) s≤ proj₂ (Simple/cost.poke c₂))

-- simple₁/cost≤simple₂/cost : simple₁/cost s≤ simple₂/cost false
-- _s≤_.poke simple₁/cost≤simple₂/cost = {!   !} , {!   !}
