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
open import Calf.Types.Bool
open import Calf.Types.Maybe
open import Calf.Types.Nat
open import Calf.Types.List
open import Data.Nat as Nat using (_+_; _∸_; pred; _*_; _^_; _>_)
open import Data.Product
import Data.Nat.Properties as Nat
open import Data.Nat.PredExp2
import Data.List.Properties as List

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

variable
  A B C D E : tp pos
  X Y Z : tp neg

record StepCommutative : Set where
  field
    bind/bind : {A B : tp pos} {X : tp neg}
      (e₁ : cmp (F A)) (e₂ : cmp (F B)) (f : val A → val B → cmp X) →
        (bind X e₁ λ x₁ → bind X e₂ λ x₂ → f x₁ x₂) ≡ (bind X e₂ λ x₂ → bind X e₁ λ x₁ → f x₁ x₂)



module Simple where
  record Simple : Set
  simple : tp neg

  record Simple where
    coinductive
    field
      here : cmp (F unit)
      next : cmp simple
  simple = meta Simple

  postulate
    here/step : ∀ {c e} → Simple.here (step simple c e) ≡ step (F unit) c (Simple.here e)
    next/step : ∀ {c e} → Simple.next (step simple c e) ≡ step simple   c (Simple.next e)
  {-# REWRITE here/step next/step #-}

  {-# TERMINATING #-}
  every : cmp simple
  Simple.here every = ret triv
  Simple.next every = step simple 1 every

  Φ : val bool → ℂ
  Φ false = 1
  Φ true  = 0

  {-# TERMINATING #-}
  alternating : cmp (Π bool λ _ → simple)
  Simple.here (alternating b) = step (F unit) (Φ b) (ret triv)
  Simple.next (alternating false) = step simple 2 (alternating true)
  Simple.next (alternating true ) = alternating false

  record _≈_ (s₁ s₂ : cmp simple) : Set where
    coinductive
    field
      here : Simple.here s₁ ≡ Simple.here s₂
      next : Simple.next s₁ ≈ Simple.next s₂

  ≈-cong : (c : cmp cost) {x y : Simple} → x ≈ y → step simple c x ≈ step simple c y
  _≈_.here (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.here h)
  _≈_.next (≈-cong c h) = ≈-cong c (_≈_.next h)

  {-# TERMINATING #-}
  every≈alternating : ∀ b → alternating b ≈ step simple (Φ b) every
  _≈_.here (every≈alternating _) = refl
  _≈_.next (every≈alternating false) = ≈-cong 2 (every≈alternating true)
  _≈_.next (every≈alternating true ) = every≈alternating false


module Queue where
  record Queue (E : tp pos) (X : tp neg) : Set
  queue : tp pos → tp neg → tp neg

  record Queue E X where
    coinductive
    field
      quit    : cmp X
      enqueue : cmp (Π E λ _ → meta (Queue E X))
      dequeue : cmp (F (prod⁺ (maybe E) (U (queue E X))))
  queue E X = meta (Queue E X)

  postulate
    quit/step    : ∀ {c e} → Queue.quit    (step (queue E X) c e) ≡ step X                                     c (Queue.quit e)
    enqueue/step : ∀ {c e} → Queue.enqueue (step (queue E X) c e) ≡ step (Π E λ _ → queue E X)                 c (Queue.enqueue e)
    dequeue/step : ∀ {c e} → Queue.dequeue (step (queue E X) c e) ≡ step (F (prod⁺ (maybe E) (U (queue E X)))) c (Queue.dequeue e)
  {-# REWRITE enqueue/step dequeue/step quit/step #-}

  {-# TERMINATING #-}
  list-queue : cmp (Π (list E) λ _ → queue E (F unit))
  Queue.quit (list-queue l) = ret triv
  Queue.enqueue (list-queue {E} l) e = step (queue E (F unit)) (length l) (list-queue (l ++ [ e ]))
  Queue.dequeue (list-queue []) = ret (nothing , list-queue [])
  Queue.dequeue (list-queue (e ∷ l)) = ret (just e , list-queue l)

  {-# TERMINATING #-}
  SPEC/list-queue : cmp (Π (list E) λ _ → queue E (F unit))
  Queue.enqueue (SPEC/list-queue {E} l) e = step (queue E (F unit)) 1 (SPEC/list-queue (l ++ [ e ]))
  Queue.dequeue (SPEC/list-queue []) = ret (nothing , SPEC/list-queue [])
  Queue.dequeue (SPEC/list-queue (e ∷ l)) = ret (just e , SPEC/list-queue l)
  Queue.quit (SPEC/list-queue l) = ret triv

  Φ : val (list E) → val (list E) → ℂ
  Φ bl fl = length bl

  {-# TERMINATING #-}
  batched-queue : cmp (Π (list E) λ _ → Π (list E) λ _ → queue E (F unit))
  Queue.quit (batched-queue {E} bl fl) = step (F unit) (Φ {E} bl fl) (ret triv)
  Queue.enqueue (batched-queue bl fl) e = batched-queue (e ∷ bl) fl
  Queue.dequeue (batched-queue {E} bl []) with reverse bl
  ... | [] = ret (nothing , batched-queue [] [])
  ... | e ∷ fl = step (F (prod⁺ (maybe E) (U (queue E (F unit))))) (length bl) (ret (just e , batched-queue [] fl))
  Queue.dequeue (batched-queue bl (e ∷ fl)) = ret (just e , batched-queue bl fl)

  {-# TERMINATING #-}
  SPEC/batched-queue : cmp (Π (list E) λ _ → Π (list E) λ _ → queue E (F unit))
  Queue.quit (SPEC/batched-queue bl fl) = ret triv
  Queue.enqueue (SPEC/batched-queue {E} bl fl) e = step (queue E (F unit)) 1 (SPEC/batched-queue (e ∷ bl) fl)
  Queue.dequeue (SPEC/batched-queue bl []) with reverse bl
  ... | [] = ret (nothing , SPEC/batched-queue [] [])
  ... | e ∷ fl = ret (just e , SPEC/batched-queue [] fl)
  Queue.dequeue (SPEC/batched-queue bl (e ∷ fl)) = ret (just e , SPEC/batched-queue bl fl)

  record _≈_ {E : tp pos} {X : tp neg} (q₁ q₂ : cmp (queue E X)) : Set where
    coinductive
    field
      quit    : cmp (F (U (meta (Queue.quit q₁ ≡ Queue.quit q₂))))
      enqueue : cmp (Π E λ e → meta (Queue.enqueue q₁ e ≈ Queue.enqueue q₂ e))
      dequeue :
        ◯ (cmp (F (U (meta (bind (F (maybe E)) (Queue.dequeue q₁) (ret ∘ proj₁) ≡ bind (F (maybe E)) (Queue.dequeue q₂) (ret ∘ proj₁)))))) ×
        (bind (queue E X) (Queue.dequeue q₁) proj₂ ≈ bind (queue E X) (Queue.dequeue q₂) proj₂)

  ≈-cong : (c : ℂ) {x y : Queue E X} → x ≈ y → step (queue E X) c x ≈ step (queue E X) c y
  _≈_.quit (≈-cong {X = X} c {x} {y} h) = bind (F (U (meta (step X c (Queue.quit x) ≡ step X c (Queue.quit y))))) (_≈_.quit h) (ret ∘ Eq.cong (step X c))
  _≈_.enqueue (≈-cong c h) e = ≈-cong c (_≈_.enqueue h e)
  _≈_.dequeue (≈-cong {E} {X} c {x} {y} h) =
    (λ u →
      bind
        (F (U (meta (step (F (maybe E)) c (bind (F (maybe E)) (Queue.dequeue x) (ret ∘ proj₁)) ≡ step (F (maybe E)) c (bind (F (maybe E)) (Queue.dequeue y) (ret ∘ proj₁))))))
        (proj₁ (_≈_.dequeue h) u)
        (ret ∘ Eq.cong (step (F (maybe E)) c))) ,
    ≈-cong c (proj₂ (_≈_.dequeue h))

  {-# TERMINATING #-}
  batched-queue≈SPEC/batched-queue : (bl fl : val (list E)) →
    batched-queue bl fl ≈ step (queue E (F unit)) (Φ {E} bl fl) (SPEC/batched-queue bl fl)
  _≈_.quit (batched-queue≈SPEC/batched-queue bl fl) = ret refl
  _≈_.enqueue (batched-queue≈SPEC/batched-queue {E} bl fl) e =
    Eq.subst
      (λ c → batched-queue (e ∷ bl) fl ≈ step (queue E (F unit)) c (SPEC/batched-queue (e ∷ bl) fl))
      (Nat.+-comm 1 (length bl))
      (batched-queue≈SPEC/batched-queue (e ∷ bl) fl)
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  ... | [] | h with h refl
  ... | refl = (λ u → ret refl) , batched-queue≈SPEC/batched-queue [] []
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) | e ∷ fl | _ =
    (λ u → ret refl) , ≈-cong (length bl) (batched-queue≈SPEC/batched-queue [] fl)
  _≈_.dequeue (batched-queue≈SPEC/batched-queue {E} bl (e ∷ fl)) =
    (λ u → ret (Eq.sym (step/ext (F (maybe E)) (ret (just e)) (Φ {E} bl fl) u))) ,
    batched-queue≈SPEC/batched-queue bl fl

  {-# TERMINATING #-}
  batched-queue≈SPEC/list-queue : (bl fl : val (list E)) →
    batched-queue bl fl ≈ step (queue E (F unit)) (Φ {E} bl fl) (SPEC/list-queue (fl ++ reverse bl))
  _≈_.quit (batched-queue≈SPEC/list-queue bl fl) = ret refl
  _≈_.enqueue (batched-queue≈SPEC/list-queue {E} bl fl) e =
    Eq.subst₂
      (λ c l → batched-queue (e ∷ bl) fl ≈ step (queue E (F unit)) c (SPEC/list-queue l))
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
  ... | [] | h with h refl
  ... | refl =
    (λ u → ret refl) , batched-queue≈SPEC/list-queue [] []
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl []) | e ∷ fl | _ =
    (λ u → ret refl) ,
    ≈-cong (length bl)
      ( Eq.subst
          (λ l → batched-queue [] fl ≈ SPEC/list-queue l)
          (List.++-identityʳ fl)
          (batched-queue≈SPEC/list-queue [] fl)
      )
  _≈_.dequeue (batched-queue≈SPEC/list-queue {E} bl (e ∷ fl)) =
    (λ u → ret (Eq.sym (step/ext (F (maybe E)) (ret (just e)) (Φ {E} bl fl) u))) ,
    batched-queue≈SPEC/list-queue bl fl


  {-# TERMINATING #-}
  ◯[list-queue≈batched-queue] : (bl fl : val (list E)) → ◯ (list-queue {E} (fl ++ reverse bl) ≈ batched-queue bl fl)
  _≈_.quit (◯[list-queue≈batched-queue] bl fl u) = ret (Eq.sym (step/ext (F unit) (ret triv) (length bl) u))
  _≈_.enqueue (◯[list-queue≈batched-queue] {E} bl fl u) e =
    Eq.subst
      (_≈ Queue.enqueue (batched-queue bl fl) e)
      (Eq.sym (step/ext (queue E (F unit)) (list-queue _) (length (fl ++ reverse bl)) u))
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
        (◯[list-queue≈batched-queue] {E} (e ∷ bl) fl u))
  _≈_.dequeue (◯[list-queue≈batched-queue] bl [] u) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  ... | [] | h with h refl
  ... | refl =
    (λ u → ret refl) , ◯[list-queue≈batched-queue] [] [] u
  _≈_.dequeue (◯[list-queue≈batched-queue] {E} bl [] u) | e ∷ fl | _ =
    (λ u → ret (Eq.sym (step/ext (F (maybe E)) (ret (just e)) (Φ {E} bl fl) u))) ,
    Eq.subst₂
      _≈_
      (Eq.cong list-queue (List.++-identityʳ fl))
      (Eq.sym (step/ext (queue E (F unit)) (batched-queue [] fl) (Φ {E} bl fl) u))
      (◯[list-queue≈batched-queue] [] fl u)
  _≈_.dequeue (◯[list-queue≈batched-queue] bl (e ∷ fl) u) =
    (λ u → ret refl) , ◯[list-queue≈batched-queue] bl fl u

  -- {-# TERMINATING #-}
  -- fake-queue : cmp (queue E (F unit))
  -- Queue.quit fake-queue = ret triv
  -- Queue.enqueue fake-queue e = fake-queue
  -- Queue.dequeue fake-queue = ret (nothing , fake-queue)

  -- issue : (c₁ c₂ : ℂ) → step (queue E (F unit)) c₁ fake-queue ≈ step (queue E (F unit)) c₂ fake-queue
  -- _≈_.quit (issue c₁ c₂) = {!   !}
  -- _≈_.enqueue (issue c₁ c₂) e = issue c₁ c₂
  -- _≈_.dequeue (issue c₁ c₂) =
  --   c₁ , nothing , fake-queue , refl ,
  --   c₂ , nothing , fake-queue , refl ,
  --   refl , issue c₁ c₂

  data QueueProgram (E : tp pos) (A : tp pos) : Set
  queue-program : tp pos → tp pos → tp pos

  data QueueProgram E A where
    return : val A → QueueProgram E A
    enqueue : val E → val (queue-program E A) → QueueProgram E A
    dequeue : val (U (Π (maybe E) λ _ → F (queue-program E A))) → QueueProgram E A
  queue-program E A = U (meta (QueueProgram E A))

  {-# TERMINATING #-}
  ψ : cmp (Π (queue-program E A) λ _ → Π (U (queue E (F unit))) λ _ → F A)
  ψ {A = A} (return b) q = bind (F A) (Queue.quit q) λ _ → ret b
  ψ (enqueue e p) q = ψ p (Queue.enqueue q e)
  ψ {A = A} (dequeue f) q =
    bind (F A) (Queue.dequeue q) λ (e , q') →
    bind (F A) (f e) λ p' →
    ψ p' q'

  step-ψ : ∀ c p q → step (F A) c (ψ p q) ≡ ψ p (step (queue E (F unit)) c q)
  step-ψ c (return x) q = refl
  step-ψ c (enqueue e p) q = step-ψ c p (Queue.enqueue q e)
  step-ψ c (dequeue f) q = refl

  postulate
    step-ret-injective : (c₁ c₂ : ℂ) (v₁ v₂ : val A) →
      step (F A) c₁ (ret v₁) ≡ step (F A) c₂ (ret v₂) → v₁ ≡ v₂

  _≈'_ : {E : tp pos} (q₁ q₂ : cmp (queue E (F unit))) → Set
  _≈'_ {E} q₁ q₂ = ∀ A → cmp (Π (queue-program E A) λ p → F (U (meta (ψ p q₁ ≡ ψ p q₂))))

  {-# TERMINATING #-}
  classic-amortization :
    StepCommutative
    → {q₁ q₂ : cmp (queue E (F unit))}
    → q₁ ≈ q₂ ⇔ q₁ ≈' q₂
  classic-amortization {E} comm = record
    { f = forward
    ; g = backward
    ; cong₁ = Eq.cong forward
    ; cong₂ = Eq.cong backward
    }
    where
      forward : {q₁ q₂ : cmp (queue E (F unit))} →
        q₁ ≈ q₂ → q₁ ≈' q₂
      forward {q₁} {q₂} h A (return x) =
        bind (F (U (meta (ψ (return x) q₁ ≡ ψ (return x) q₂)))) (_≈_.quit h) λ h →
        ret (Eq.cong (λ e → bind (F A) e (const (ret x))) h)
      forward h A (enqueue e p) = forward (_≈_.enqueue h e) A p
      forward {q₁} {q₂} h A (dequeue f) =
        ret (
      -- with _≈_.dequeue h
      -- ... | c₁ , e , q₁' , h₁ , c₂ , _ , q₂' , h₂ , refl , hq' =
        let open ≡-Reasoning in
        begin
          ( bind (F A) (Queue.dequeue q₁) λ (e , q₁') →
            bind (F A) (f e) λ p' →
            ψ p' q₁' )
        -- ≡⟨ Eq.cong (λ e → bind (F A) e λ (e , q₁') → bind (F A) (f e) λ p' → ψ p' q₁') h₁ ⟩
        --   (bind (F A) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₁ (ret (e , q₁'))) λ (e , q₁') →
        --   bind (F A) (f e) λ p' →
        --   ψ p' q₁')
        -- ≡⟨⟩
        --   step (F A) c₁ (
        --   bind (F A) (f e) λ p' →
        --   ψ p' q₁')
        -- ≡˘⟨ bind/step/commutative {B = A} {c = c₁} {e = f e} ⟩
        --   (bind (F A) (f e) λ p' →
        --   step (F A) c₁ (ψ p' q₁'))
        -- ≡⟨
        --   Eq.cong (bind (F A) (f e)) (funext λ p' →
        --   begin
        --     step (F A) c₁ (ψ p' q₁')
        --   ≡⟨ step-ψ c₁ p' q₁' ⟩
        --     ψ p' (step (queue E (F unit)) c₁ q₁')
        --   ≡⟨ forward (step (queue E (F unit)) c₁ q₁') (step (queue E (F unit)) c₂ q₂') hq' A p' ⟩
        --     ψ p' (step (queue E (F unit)) c₂ q₂')
        --   ≡˘⟨ step-ψ c₂ p' q₂' ⟩
        --     step (F A) c₂ (ψ p' q₂')
        --   ∎)
        -- ⟩
        --   (bind (F A) (f e) λ p' →
        --   step (F A) c₂ (ψ p' q₂'))
        -- ≡⟨ bind/step/commutative {B = A} {c = c₂} {e = f e} ⟩
        --   step (F A) c₂ (
        --   bind (F A) (f e) λ p' →
        --   ψ p' q₂')
        -- ≡⟨⟩
        --   (bind (F A) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₂ (ret (e , q₂'))) λ (e , q₂') →
        --   bind (F A) (f e) λ p' →
        --   ψ p' q₂')
        -- ≡˘⟨ Eq.cong (λ e → bind (F A) e λ (e , q₂') → bind (F A) (f e) λ p' → ψ p' q₂') h₂ ⟩
        ≡⟨ {! forward (proj₂ (_≈_.dequeue h)) A ?  !} ⟩
          ( bind (F A) (Queue.dequeue q₂) λ (e , q₂') →
            bind (F A) (f e) λ p' →
            ψ p' q₂' )
        ∎)

      bind-ψ : ∀ {B A} (e : cmp (F B)) f p → bind (F A) e (ψ p ∘ f) ≡ ψ p (bind (queue E (F unit)) e f)
      bind-ψ = {!   !}

      backward : {q₁ q₂ : cmp (queue E (F unit))} →
        q₁ ≈' q₂ → q₁ ≈ q₂
      _≈_.quit (backward typical) = typical unit (return triv)
      _≈_.enqueue (backward typical) e =
        backward (λ A p → typical A (enqueue e p))
      _≈_.dequeue (backward {q₁} {q₂} typical) =
        (λ u →
          bind (F (U (meta (bind (F (maybe E)) (Queue.dequeue q₁) (ret ∘ proj₁) ≡ bind (F (maybe E)) (Queue.dequeue q₂) (ret ∘ proj₁))))) (typical (maybe E) (dequeue (λ e → ret (return e)))) λ h →
          ret
            ( let open ≡-Reasoning in
              begin
                bind (F (maybe E)) (Queue.dequeue q₁) (ret ∘ proj₁)
              ≡⟨ {!   !} ⟩
                ( bind (F (maybe E)) (Queue.dequeue q₁) λ (e , q₁') →
                  bind (F (maybe E)) (Queue.quit q₁') λ _ →
                  ret e )
              ≡⟨⟩
                ψ (dequeue (λ e → ret (return e))) q₁
              ≡⟨ h ⟩
                ψ (dequeue (λ e → ret (return e))) q₂
              ≡⟨⟩
                ( bind (F (maybe E)) (Queue.dequeue q₂) λ (e , q₂') →
                  bind (F (maybe E)) (Queue.quit q₂') λ _ →
                  ret e )
              ≡⟨ {!   !} ⟩
                bind (F (maybe E)) (Queue.dequeue q₂) (ret ∘ proj₁)
              ∎
            )) ,
        backward (λ A p →
          bind (F (U (meta (ψ p _ ≡ ψ p _)))) (typical A (dequeue (const (ret p)))) λ h →
          ret
            ( let open ≡-Reasoning in
              begin
                ψ p (bind (queue E (F unit)) (Queue.dequeue q₁) proj₂)
              ≡˘⟨ bind-ψ (Queue.dequeue q₁) proj₂ p ⟩
                bind (F A) (Queue.dequeue q₁) (ψ p ∘ proj₂)
              ≡⟨ h ⟩
                bind (F A) (Queue.dequeue q₂) (ψ p ∘ proj₂)
              ≡⟨ bind-ψ (Queue.dequeue q₂) proj₂ p ⟩
                ψ p (bind (queue E (F unit)) (Queue.dequeue q₂) proj₂)
              ∎
            ))


module DynamicArray where
  record DynamicArray (A : tp pos) : Set where
    coinductive
    field
      quit : cmp (F unit)
      append : cmp (Π A λ _ → meta (DynamicArray A))
      get : cmp (Π nat λ _ → F (prod⁺ (maybe A) (U (meta (DynamicArray A)))))
  dynamic-array : tp pos → tp neg
  dynamic-array A = meta (DynamicArray A)

  postulate
    quit/step   : ∀ {c e} → DynamicArray.quit   (step (dynamic-array A) c e) ≡ step (F unit)                                                      c (DynamicArray.quit   e)
    append/step : ∀ {c e} → DynamicArray.append (step (dynamic-array A) c e) ≡ step (Π A λ _ → dynamic-array A)                                   c (DynamicArray.append e)
    get/step    : ∀ {c e} → DynamicArray.get    (step (dynamic-array A) c e) ≡ step (Π nat λ _ → F (prod⁺ (maybe A) (U (meta (DynamicArray A))))) c (DynamicArray.get    e)
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
  ... | no ¬p = ret (nothing , array n m)
  ... | yes p = ret (just triv , array n m)

  {-# TERMINATING #-}
  SPEC/array : cmp (Π nat λ _ → dynamic-array unit)
  DynamicArray.quit (SPEC/array n) = ret triv
  DynamicArray.append (SPEC/array n) triv = step (dynamic-array unit) 2 (SPEC/array (suc n))
  DynamicArray.get (SPEC/array n) i with i Nat.<? n
  ... | no ¬p = ret (nothing , SPEC/array n)
  ... | yes p = ret (just triv , SPEC/array n)

  record _≈_ {A : tp pos} (d₁ d₂ : cmp (dynamic-array A)) : Set where
    coinductive
    field
      quit : DynamicArray.quit d₁ ≡ DynamicArray.quit d₂
      append : cmp (Π A λ a → meta (DynamicArray.append d₁ a ≈ DynamicArray.append d₂ a))
      get :
        (i : val nat) →
          Σ ℂ λ c₁ → Σ (val (maybe A)) λ a₁ → Σ (cmp (dynamic-array A)) λ d₁' → DynamicArray.get d₁ i ≡ step (F (prod⁺ (maybe A) (U (meta (DynamicArray A))))) c₁ (ret (a₁ , d₁')) ×
          Σ ℂ λ c₂ → Σ (val (maybe A)) λ a₂ → Σ (cmp (dynamic-array A)) λ d₂' → DynamicArray.get d₂ i ≡ step (F (prod⁺ (maybe A) (U (meta (DynamicArray A))))) c₂ (ret (a₂ , d₂')) ×
          -- (c₁ ≡ c₂) ×  -- not amortized
          (a₁ ≡ a₂) ×
          -- (d₁' ≈ d₂')  -- not amortized
          (step (dynamic-array A) c₁ d₁' ≈ step (dynamic-array A) c₂ d₂')  -- amortized

  ≈-cong : (c : cmp cost) {x y : DynamicArray A} → x ≈ y → step (dynamic-array A) c x ≈ step (dynamic-array A) c y
  _≈_.quit (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.quit h)
  _≈_.append (≈-cong c h) a = ≈-cong c (_≈_.append h a)
  _≈_.get (≈-cong {A} c h) i =
    let (c₁ , a₁ , d₁' , h₁ , c₂ , a₂ , d₂' , h₂ , ha , hd') = _≈_.get h i in
    c + c₁ , a₁ , d₁' , Eq.cong (step (F (prod⁺ (maybe A) (U (dynamic-array A)))) c) h₁ ,
    c + c₂ , a₂ , d₂' , Eq.cong (step (F (prod⁺ (maybe A) (U (dynamic-array A)))) c) h₂ ,
    ha , ≈-cong c hd'

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
  ... | no ¬p =
          zero , nothing , array n m , refl ,
          2 ^ n ∸ 2 * m , nothing , SPEC/array (2 ^ n ∸ m) , refl ,
          refl , array≈SPEC/array n m h
  ... | yes p =
          zero , just triv , array n m , refl ,
          2 ^ n ∸ 2 * m , just triv , SPEC/array (2 ^ n ∸ m) , refl ,
          refl , array≈SPEC/array n m h
