module Examples.Amortized where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Level using (0ℓ)

open import Calf costMonoid
open import Calf.Types.Unit
open import Calf.Types.Product
open import Calf.Types.Bool
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.List
open import Data.Nat as Nat using (_+_; _∸_; pred; _*_; _^_; _>_)
open import Data.Product
open import Data.Nat.Properties as Nat using (module ≤-Reasoning)
open import Data.Nat.PredExp2
open import Data.Nat.Logarithm
import Data.List.Properties as List

open import Function hiding (_⇔_)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

variable
  A B C : tp pos
  X Y Z : tp neg

_⋉_ : tp pos → tp neg → tp neg
A ⋉ X = Σ+- A (const X)

infix 3 _⇒_ _⇔_
_⇒_ _⇔_ : tp neg → tp neg → tp neg
X ⇒ Y = Π (U X) λ _ → Y
X ⇔ Y = prod⁻ (X ⇒ Y) (Y ⇒ X)


module Simple where
  postulate
    simple : tp neg
  record Simple : Set where
    coinductive
    field
      quit : cmp (F unit)
      next : cmp simple
  postulate
    simple/decode : val (U simple) ≡ Simple
    {-# REWRITE simple/decode #-}

    quit/step : ∀ {c e} → Simple.quit (step simple c e) ≡ step (F unit) c (Simple.quit e)
    next/step : ∀ {c e} → Simple.next (step simple c e) ≡ step simple   c (Simple.next e)
    {-# REWRITE quit/step next/step #-}

  {-# TERMINATING #-}
  every : cmp simple
  Simple.quit every = ret triv
  Simple.next every = step simple 1 every

  Φ : val bool → ℂ
  Φ false = 1
  Φ true  = 0

  {-# TERMINATING #-}
  alternating : cmp (Π bool λ _ → simple)
  Simple.quit (alternating b) = step (F unit) (Φ b) (ret triv)
  Simple.next (alternating false) = step simple 2 (alternating true)
  Simple.next (alternating true ) = alternating false

  record _≈_ (s₁ s₂ : cmp simple) : Set where
    coinductive
    field
      quit : Simple.quit s₁ ≡ Simple.quit s₂
      next : Simple.next s₁ ≈ Simple.next s₂

  ≈-cong : (c : cmp cost) {x y : Simple} → x ≈ y → step simple c x ≈ step simple c y
  _≈_.quit (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.quit h)
  _≈_.next (≈-cong c h) = ≈-cong c (_≈_.next h)

  {-# TERMINATING #-}
  every≈alternating : ∀ b → alternating b ≈ step simple (Φ b) every
  _≈_.quit (every≈alternating _) = refl
  _≈_.next (every≈alternating false) = ≈-cong 2 (every≈alternating true)
  _≈_.next (every≈alternating true ) = every≈alternating false

  simple-program : tp pos
  simple-program = nat

  {-# TERMINATING #-}
  ψ : cmp (Π simple-program λ _ → Π (U simple) λ _ → F unit)
  ψ zero    s = Simple.quit s
  ψ (suc n) s = ψ n (Simple.next s)

  _≈'_ : (q₁ q₂ : cmp simple) → Set
  s₁ ≈' s₂ = cmp (Π simple-program λ p → meta (ψ p s₁ ≡ ψ p s₂))

  {-# TERMINATING #-}
  classic-amortization : {s₁ s₂ : cmp simple} → cmp (meta (s₁ ≈ s₂) ⇔ meta (s₁ ≈' s₂))
  classic-amortization = forward , backward
    where
      forward : {s₁ s₂ : cmp simple} → s₁ ≈ s₂ → s₁ ≈' s₂
      forward h zero    = _≈_.quit h
      forward h (suc n) = forward (_≈_.next h) n

      backward : {s₁ s₂ : cmp simple} → s₁ ≈' s₂ → s₁ ≈ s₂
      _≈_.quit (backward classic) = classic zero
      _≈_.next (backward classic) = backward (λ n → classic (suc n))


module Queue where
  -- moving `E` to a parameter on `module Queue` breaks things - Agda bug?
  E : tp pos
  E = nat

  postulate
    queue : tp neg → tp neg
  record Queue (X : tp neg) : Set where
    coinductive
    field
      quit    : cmp X
      enqueue : cmp (Π E λ _ → queue X)
      dequeue : cmp (maybe E ⋉ queue X)
  postulate
    queue/decode : val (U (queue X)) ≡ Queue X
    {-# REWRITE queue/decode #-}

    quit/step    : ∀ {c e} → Queue.quit    (step (queue X) c e) ≡ step X                   c (Queue.quit e)
    enqueue/step : ∀ {c e} → Queue.enqueue (step (queue X) c e) ≡ step (Π E λ _ → queue X) c (Queue.enqueue e)
    dequeue/step : ∀ {c e} → Queue.dequeue (step (queue X) c e) ≡ step (maybe E ⋉ queue X) c (Queue.dequeue e)
    {-# REWRITE quit/step enqueue/step dequeue/step #-}

  {-# TERMINATING #-}
  list-queue : cmp (Π (list E) λ _ → queue (F unit))
  Queue.quit (list-queue l) = ret triv
  Queue.enqueue (list-queue l) e = step (queue (F unit)) (length l) (list-queue (l ++ [ e ]))
  Queue.dequeue (list-queue []     ) = nothing , list-queue []
  Queue.dequeue (list-queue (e ∷ l)) = just e , list-queue l

  {-# TERMINATING #-}
  SPEC/list-queue : cmp (Π (list E) λ _ → queue (F unit))
  Queue.quit (SPEC/list-queue l) = ret triv
  Queue.enqueue (SPEC/list-queue l) e = step (queue (F unit)) 1 (SPEC/list-queue (l ++ [ e ]))
  Queue.dequeue (SPEC/list-queue []     ) = nothing , SPEC/list-queue []
  Queue.dequeue (SPEC/list-queue (e ∷ l)) = just e , SPEC/list-queue l

  Φ : val (list E) → val (list E) → ℂ
  Φ bl fl = length bl

  {-# TERMINATING #-}
  batched-queue : cmp (Π (list E) λ _ → Π (list E) λ _ → queue (F unit))
  Queue.quit (batched-queue bl fl) = step (F unit) (Φ bl fl) (ret triv)
  Queue.enqueue (batched-queue bl fl) e = batched-queue (e ∷ bl) fl
  Queue.dequeue (batched-queue bl []) with reverse bl
  ... | [] = nothing , batched-queue [] []
  ... | e ∷ fl = step (maybe E ⋉ queue (F unit)) (length bl) (just e , batched-queue [] fl)
  Queue.dequeue (batched-queue bl (e ∷ fl)) = just e , batched-queue bl fl

  {-# TERMINATING #-}
  SPEC/batched-queue : cmp (Π (list E) λ _ → Π (list E) λ _ → queue (F unit))
  Queue.quit (SPEC/batched-queue bl fl) = ret triv
  Queue.enqueue (SPEC/batched-queue bl fl) e = step (queue (F unit)) 1 (SPEC/batched-queue (e ∷ bl) fl)
  Queue.dequeue (SPEC/batched-queue bl []) with reverse bl
  ... | [] = nothing , SPEC/batched-queue [] []
  ... | e ∷ fl = just e , SPEC/batched-queue [] fl
  Queue.dequeue (SPEC/batched-queue bl (e ∷ fl)) = just e , SPEC/batched-queue bl fl

  record _≈_ (q₁ q₂ : cmp (queue X)) : Set where
    coinductive
    field
      quit    : cmp $
        meta (Queue.quit q₁ ≡ Queue.quit q₂)
      enqueue : cmp $
        Π E λ e → meta (Queue.enqueue q₁ e ≈ Queue.enqueue q₂ e)
      dequeue : cmp $
        (U (meta (proj₁ (Queue.dequeue q₁) ≡ proj₁ (Queue.dequeue q₂)))) ⋉
        (meta (proj₂ (Queue.dequeue q₁) ≈ proj₂ (Queue.dequeue q₂)))

  ≈-cong : (c : ℂ) {x y : Queue X} → x ≈ y → step (queue X) c x ≈ step (queue X) c y
  _≈_.quit (≈-cong {X = X} c h) = Eq.cong (step X c) (_≈_.quit h)
  _≈_.enqueue (≈-cong c h) e = ≈-cong c (_≈_.enqueue h e)
  _≈_.dequeue (≈-cong c h) = proj₁ (_≈_.dequeue h) , ≈-cong c (proj₂ (_≈_.dequeue h))

  {-# TERMINATING #-}
  batched-queue≈SPEC/batched-queue : (bl fl : val (list E)) →
    batched-queue bl fl ≈ step (queue (F unit)) (Φ bl fl) (SPEC/batched-queue bl fl)
  _≈_.quit (batched-queue≈SPEC/batched-queue bl fl) = refl
  _≈_.enqueue (batched-queue≈SPEC/batched-queue bl fl) e =
    Eq.subst
      (λ c → batched-queue (e ∷ bl) fl ≈ step (queue (F unit)) c (SPEC/batched-queue (e ∷ bl) fl))
      (Nat.+-comm 1 (length bl))
      (batched-queue≈SPEC/batched-queue (e ∷ bl) fl)
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) | [] | h with h refl
  ... | refl = refl , batched-queue≈SPEC/batched-queue [] []
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) | e ∷ fl | _ =
    refl , ≈-cong (Φ bl fl) (batched-queue≈SPEC/batched-queue [] fl)
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl (e ∷ fl)) =
    refl , batched-queue≈SPEC/batched-queue bl fl

  {-# TERMINATING #-}
  batched-queue≈SPEC/list-queue : (bl fl : val (list E)) →
    batched-queue bl fl ≈ step (queue (F unit)) (Φ bl fl) (SPEC/list-queue (fl ++ reverse bl))
  _≈_.quit (batched-queue≈SPEC/list-queue bl fl) = refl
  _≈_.enqueue (batched-queue≈SPEC/list-queue bl fl) e =
    Eq.subst₂
      (λ c l → batched-queue (e ∷ bl) fl ≈ step (queue (F unit)) c (SPEC/list-queue l))
      (Nat.+-comm 1 (length bl))
      (let open ≡-Reasoning in
      begin
        fl ++ reverse (e ∷ bl)
      ≡⟨ Eq.cong (fl ++_) (List.unfold-reverse e bl) ⟩
        fl ++ reverse bl ∷ʳ e
      ≡˘⟨ List.++-assoc fl (reverse bl) [ e ] ⟩
        (fl ++ reverse bl) ∷ʳ e
      ∎)
      (batched-queue≈SPEC/list-queue (e ∷ bl) fl)
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl []) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl []) | [] | h with h refl
  ... | refl = refl , batched-queue≈SPEC/list-queue [] []
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl []) | e ∷ fl | _ =
    refl ,
    ≈-cong (length bl)
      ( Eq.subst
          (λ l → batched-queue [] fl ≈ SPEC/list-queue l)
          (List.++-identityʳ fl)
          (batched-queue≈SPEC/list-queue [] fl)
      )
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl (e ∷ fl)) =
    refl , batched-queue≈SPEC/list-queue bl fl

  -- {-# TERMINATING #-}
  -- fake-queue : cmp (queue (F unit))
  -- Queue.quit fake-queue = ret triv
  -- Queue.enqueue fake-queue e = fake-queue
  -- Queue.dequeue fake-queue = nothing , fake-queue

  -- issue : (c₁ c₂ : ℂ) → step (queue (F unit)) c₁ fake-queue ≈ step (queue (F unit)) c₂ fake-queue
  -- _≈_.quit (issue c₁ c₂) = {!   !}
  -- _≈_.enqueue (issue c₁ c₂) e = issue c₁ c₂
  -- _≈_.dequeue (issue c₁ c₂) = refl , issue c₁ c₂


  {-# TERMINATING #-}
  ◯[list-queue≈batched-queue] : (bl fl : val (list E)) → ◯ (list-queue (fl ++ reverse bl) ≈ batched-queue bl fl)
  _≈_.quit (◯[list-queue≈batched-queue] bl fl u) =
    Eq.sym (step/ext (F unit) (ret triv) (length bl) u)
  _≈_.enqueue (◯[list-queue≈batched-queue] bl fl u) e =
    Eq.subst
      (_≈ Queue.enqueue (batched-queue bl fl) e)
      (Eq.sym (step/ext (queue (F unit)) (list-queue _) (length (fl ++ reverse bl)) u))
      (Eq.subst
        (λ l → list-queue l ≈ batched-queue (e ∷ bl) fl)
        {x = fl ++ reverse (e ∷ bl)}
        (let open ≡-Reasoning in
        begin
          fl ++ reverse (e ∷ bl)
        ≡⟨ Eq.cong (fl ++_) (List.unfold-reverse e bl) ⟩
          fl ++ reverse bl ∷ʳ e
        ≡˘⟨ List.++-assoc fl (reverse bl) [ e ] ⟩
          (fl ++ reverse bl) ∷ʳ e
        ∎)
        (◯[list-queue≈batched-queue] (e ∷ bl) fl u))
  _≈_.dequeue (◯[list-queue≈batched-queue] bl [] u) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  _≈_.dequeue (◯[list-queue≈batched-queue] bl [] u) | [] | h with h refl
  ... | refl = refl , ◯[list-queue≈batched-queue] [] [] u
  _≈_.dequeue (◯[list-queue≈batched-queue] bl [] u) | e ∷ fl | _ =
    refl ,
    Eq.subst₂
      _≈_
      (Eq.cong list-queue (List.++-identityʳ fl))
      (Eq.sym (step/ext (queue (F unit)) (batched-queue [] fl) (Φ bl fl) u))
      (◯[list-queue≈batched-queue] [] fl u)
  _≈_.dequeue (◯[list-queue≈batched-queue] bl (e ∷ fl) u) =
    refl , ◯[list-queue≈batched-queue] bl fl u


  postulate
    queue-program : tp pos → tp pos
  data QueueProgram (A : tp pos) : Set where
    return  : val A → QueueProgram A
    enqueue : val E → val (queue-program A) → QueueProgram A
    dequeue : val (U (Π (maybe E) λ _ → F (queue-program A))) → QueueProgram A
  postulate
    queue-program/decode : val (queue-program A) ≡ QueueProgram A
    {-# REWRITE queue-program/decode #-}

  {-# TERMINATING #-}
  ψ : cmp (Π (queue-program A) λ _ → Π (U (queue X)) λ _ → A ⋉ X)
  ψ {A} {X} (return a   ) q = a , Queue.quit q
  ψ {A} {X} (enqueue e p) q = ψ p (Queue.enqueue q e)
  ψ {A} {X} (dequeue k  ) q =
    bind (A ⋉ X) (k (proj₁ (Queue.dequeue q))) λ p →
    ψ p (proj₂ (Queue.dequeue q))

  _≈'_ : (q₁ q₂ : cmp (queue X)) → Set
  q₁ ≈' q₂ = (A : tp pos) → cmp (Π (queue-program A) λ p → meta (ψ p q₁ ≡ ψ p q₂))

  {-# TERMINATING #-}
  classic-amortization : {q₁ q₂ : cmp (queue X)} → cmp (meta (q₁ ≈ q₂) ⇔ meta (q₁ ≈' q₂))
  classic-amortization {X} = forward , backward
    where
      forward : {q₁ q₂ : cmp (queue X)} → q₁ ≈ q₂ → q₁ ≈' q₂
      forward h A (return a   ) = Eq.cong (a ,_) (_≈_.quit h)
      forward h A (enqueue e p) = forward (_≈_.enqueue h e) A p
      forward h A (dequeue k  ) =
        Eq.cong₂
          (λ e₁ e₂ → bind (A ⋉ X) (k e₁) e₂)
          (proj₁ (_≈_.dequeue h))
          (funext (forward (proj₂ (_≈_.dequeue h)) A))

      backward : {q₁ q₂ : cmp (queue X)} → q₁ ≈' q₂ → q₁ ≈ q₂
      _≈_.quit (backward classic) = Eq.cong proj₂ (classic unit (return triv))
      _≈_.enqueue (backward classic) e = backward λ A p → classic A (enqueue e p)
      _≈_.dequeue (backward classic) =
        Eq.cong proj₁ (classic (maybe E) (dequeue λ e → ret (return e))) ,
        backward λ A p → classic A (dequeue λ _ → ret p)


module DynamicArray where
  postulate
    dynamic-array : tp pos → tp neg
  record DynamicArray (A : tp pos) : Set where
    coinductive
    field
      quit   : cmp (F unit)
      append : cmp (Π A λ _ → dynamic-array A)
      get    : cmp (Π nat λ _ → maybe A ⋉ dynamic-array A)
  postulate
    dynamic-array/decode : val (U (dynamic-array A)) ≡ DynamicArray A
    {-# REWRITE dynamic-array/decode #-}

    quit/step   : ∀ {c e} → DynamicArray.quit   (step (dynamic-array A) c e) ≡ step (F unit)                                c (DynamicArray.quit   e)
    append/step : ∀ {c e} → DynamicArray.append (step (dynamic-array A) c e) ≡ step (Π A λ _ → dynamic-array A)             c (DynamicArray.append e)
    get/step    : ∀ {c e} → DynamicArray.get    (step (dynamic-array A) c e) ≡ step (Π nat λ _ → maybe A ⋉ dynamic-array A) c (DynamicArray.get    e)
    {-# REWRITE quit/step append/step get/step #-}

  Φ : val nat → val nat → ℂ
  Φ n m = 2 ^ n ∸ 2 * m

  {-# TERMINATING #-}
  -- array n m
  -- length of allocated array: (2 ^ n)
  -- remaining free spaces: m (≤ 2 ^ (pred n))
  array : cmp (Π nat λ _ → Π nat λ _ → dynamic-array unit)
  DynamicArray.quit (array n m) = step (F unit) (Φ n m) (ret triv)
  DynamicArray.append (array n zero) triv = step (dynamic-array unit) (2 ^ n) (array (suc n) pred[2^ n ])
  DynamicArray.append (array n (suc m)) triv = array n m
  DynamicArray.get (array n m) i with i Nat.<? 2 ^ n ∸ m
  ... | no ¬p = nothing , array n m
  ... | yes p = just triv , array n m

  {-# TERMINATING #-}
  SPEC/array : cmp (Π nat λ _ → dynamic-array unit)
  DynamicArray.quit (SPEC/array n) = ret triv
  DynamicArray.append (SPEC/array n) triv = step (dynamic-array unit) 2 (SPEC/array (suc n))
  DynamicArray.get (SPEC/array n) i with i Nat.<? n
  ... | no ¬p = nothing , SPEC/array n
  ... | yes p = just triv , SPEC/array n

  record _≈_ {A : tp pos} (d₁ d₂ : cmp (dynamic-array A)) : Set where
    coinductive
    field
      quit   : cmp $
        meta (DynamicArray.quit d₁ ≡ DynamicArray.quit d₂)
      append : cmp $
        Π A λ a → meta (DynamicArray.append d₁ a ≈ DynamicArray.append d₂ a)
      get    : cmp $
        Π nat λ i →
          (U (meta (proj₁ (DynamicArray.get d₁ i) ≡ proj₁ (DynamicArray.get d₂ i)))) ⋉
          (meta (proj₂ (DynamicArray.get d₁ i) ≈ proj₂ (DynamicArray.get d₂ i)))

  ≈-cong : (c : cmp cost) {x y : DynamicArray A} → x ≈ y → step (dynamic-array A) c x ≈ step (dynamic-array A) c y
  _≈_.quit (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.quit h)
  _≈_.append (≈-cong c h) a = ≈-cong c (_≈_.append h a)
  _≈_.get (≈-cong c h) i = proj₁ (_≈_.get h i) , ≈-cong c (proj₂ (_≈_.get h i))

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
  array≈SPEC/array : (n m : val nat) → m Nat.≤ pred[2^ pred n ] →
    array n m ≈ step (dynamic-array unit) (2 ^ n ∸ 2 * m) (SPEC/array (2 ^ n ∸ m))
  _≈_.quit (array≈SPEC/array n m h) = refl
  _≈_.append (array≈SPEC/array n zero h) triv =
    Eq.subst₂
      (λ c x →
        step (dynamic-array unit) (2 ^ n) (array (suc n) (2 ^ n ∸ 1)) ≈
        step (dynamic-array unit) (2 ^ n + c) (SPEC/array x))
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
      (≈-cong (2 ^ n)
        {x = array (suc n) pred[2^ n ]}
        {y = step (dynamic-array unit) (2 ^ suc n ∸ 2 * pred[2^ n ]) (SPEC/array (2 ^ suc n ∸ pred[2^ n ]))}
        (array≈SPEC/array (suc n) pred[2^ n ] Nat.≤-refl))
  _≈_.append (array≈SPEC/array n (suc m) h) triv =
    Eq.subst₂
      (λ c x → array n m ≈ step (dynamic-array unit) c (SPEC/array x))
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
      ≡⟨ Nat.+-∸-assoc 2 lemma ⟩
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
      (array≈SPEC/array n m (Nat.<⇒≤ h))
  _≈_.get (array≈SPEC/array n m h) i with i Nat.<? 2 ^ n ∸ m
  ... | no ¬p = refl , array≈SPEC/array n m h
  ... | yes p = refl , array≈SPEC/array n m h

module SplayTree where
  E : tp pos
  E = nat

  variable
    n n' n₁ n₂ n₃ : ℕ

  postulate
    finset : tp neg → tp neg
  record FinSet (X : tp neg) : Set where
    coinductive
    field
      quit : cmp X
      find : cmp (Π nat λ _ → maybe E ⋉ finset X)
  postulate
    finset/decode : val (U (finset X)) ≡ FinSet X
    {-# REWRITE finset/decode #-}

    quit/step : ∀ {c e} → FinSet.quit (step (finset X) c e) ≡ step X                                c (FinSet.quit e)
    find/step : ∀ {c e} → FinSet.find (step (finset X) c e) ≡ step (Π nat λ _ → maybe E ⋉ finset X) c (FinSet.find e)
    {-# REWRITE quit/step find/step #-}

  -- Indexed Tree
  data ITree : ℕ → Set where
    leaf : ITree 0
    node : ITree n₁ → val E → ITree n₂ → ITree (n₁ + 1 + n₂)
  postulate
    itree : val nat → tp pos
    itree/decode : val (itree n) ≡ ITree n
    {-# REWRITE itree/decode #-}

  data Splayed : ℕ → Set where
    valid : (t : ITree n) → Splayed n
    zig   : (a : ITree n₁) (x : val E) (b : ITree n₂) (y : val E) (c : ITree n₃) → Splayed ((n₁ + 1 + n₂) + 1 + n₃)
    zag   : (a : ITree n₁) (y : val E) (b : ITree n₂) (x : val E) (c : ITree n₃) → Splayed (n₁ + 1 + (n₂ + 1 + n₃))
  postulate
    splayed : val nat → tp pos
    splayed/decode : val (splayed n) ≡ Splayed n
    {-# REWRITE splayed/decode #-}

  open import Tactic.MonoidSolver using (solve; solve-macro)

  +-assoc² : (n₁ : ℕ) {n₂ n₃ : ℕ} → n₁ + 1 + n₂ + 1 + n₃ ≡ n₁ + 1 + (n₂ + 1 + n₃)
  +-assoc² n₁ {n₂} {n₃} = solve Nat.+-0-monoid


  splay : ITree n → (i : val nat) → i Nat.< n → cmp (F (splayed n))
  splay {n} (node {n₁} {n₂} l z r) i i<n with Nat.<-cmp i n₁
  ... | tri< i<n₁ _ _ =
    bind (F (splayed _)) (splay l i i<n₁) λ
      { (valid (node a x b)) → ret (zig a x b z r)
      ; (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) →
          let
            arithmetic : n₁₁ + 1 + (n₁₂ + 1 + (n₁₃ + 1 + n₂)) ≡ n₁₁ + 1 + n₁₂ + 1 + n₁₃ + 1 + n₂
            arithmetic = solve Nat.+-0-monoid  -- can't plug in directly?
          in
          ret (Eq.subst Splayed arithmetic (valid (node a x (node b y (node c z r)))))
      ; (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) →
          let
            arithmetic : n₁₁ + 1 + n₁₂ + 1 + (n₁₃ + 1 + n₂) ≡ n₁₁ + 1 + (n₁₂ + 1 + n₁₃) + 1 + n₂
            arithmetic = solve Nat.+-0-monoid
          in
          ret (valid (Eq.subst ITree arithmetic (node (node a y b) x (node c z r))))
      }
  ... | tri≈ _ refl _ = ret (valid (node l z r))
  ... | tri> _ _ i>n₁ =
    let
      arithmetic : i ∸ (n₁ + 1) Nat.< n₂
      arithmetic =
        let open ≤-Reasoning in
        Nat.+-cancelˡ-< (n₁ + 1) (i ∸ (n₁ + 1)) n₂ $
        begin-strict
          (n₁ + 1) + (i ∸ (n₁ + 1))
        ≡⟨ Nat.m+[n∸m]≡n (Eq.subst (i Nat.≥_) (Nat.+-comm 1 n₁) i>n₁) ⟩
          i
        <⟨ i<n ⟩
          n₁ + 1 + n₂
        ∎
    in
    bind (F (splayed _)) (splay r (i ∸ (n₁ + 1)) arithmetic) λ
      { (valid leaf) → contradiction arithmetic Nat.n≮0
      ; (valid (node a x b)) → ret (zag l z a x b)
      ; (zig {n₁₁} {n₁₂} {n₁₃} a x b y c) →
          let
            arithmetic : n₁ + 1 + n₁₁ + 1 + (n₁₂ + 1 + n₁₃) ≡ n₁ + 1 + (n₁₁ + 1 + n₁₂ + 1 + n₁₃)
            arithmetic = solve Nat.+-0-monoid
          in
          ret (valid (Eq.subst ITree arithmetic (node (node l z a) x (node b y c))))
      ; (zag {n₁₁} {n₁₂} {n₁₃} a y b x c) →
          let
            arithmetic : n₁ + 1 + n₁₁ + 1 + n₁₂ + 1 + n₁₃ ≡ n₁ + 1 + (n₁₁ + 1 + (n₁₂ + 1 + n₁₃))
            arithmetic = solve Nat.+-0-monoid
          in
          ret (valid (Eq.subst ITree arithmetic (node (node (node l z a) y b) x c)))
      }

  Φ : ITree n → ℂ
  Φ leaf = 0
  Φ {n} (node t₁ _ t₂) = Φ t₁ + ⌊log₂ n ⌋ + Φ t₂

  {-# TERMINATING #-}
  splay-finset : ITree n → FinSet (F (itree n))
  FinSet.quit (splay-finset t) = ret t
  FinSet.find (splay-finset {n} t) i with i Nat.<? n
  ... | no _    = nothing , splay-finset t
  ... | yes i<n =
    bind (maybe E ⋉ finset _) (splay t i i<n) λ
      { (valid t@(node _ x _)) → just x , splay-finset t
      ; (zig {n₁} a x b y c) → just x , splay-finset (Eq.subst ITree (Eq.sym (+-assoc² n₁)) (node a x (node b y c)))
      ; (zag {n₁} a y b x c) → just x , splay-finset (Eq.subst ITree (+-assoc² n₁) (node (node a y b) x c))
      }

  joinMid : FinSet (F (itree n₁)) → val E → FinSet (F (itree n₂)) → FinSet (F (itree (n₁ + 1 + n₂)))
  joinMid s₁ x s₂ =
    bind (finset _) (FinSet.quit s₁) λ t₁ →
    bind (finset _) (FinSet.quit s₂) λ t₂ →
    splay-finset (node t₁ x t₂)

  list-to-itree : (l : val (list E)) → val (itree (length l))
  list-to-itree []      = leaf
  list-to-itree (x ∷ l) = node leaf x (list-to-itree l)
