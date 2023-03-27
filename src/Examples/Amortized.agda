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


module Simple where
  record Simple : Set
  simple : tp neg

  record Simple where
    coinductive
    field
      here : cmp (F unit)
      next : cmp simple
  simple = meta (Simple)

  postulate
    here/step : ∀ {c e} → Simple.here (step simple c e) ≡ step (F unit) c (Simple.here e)
    next/step : ∀ {c e} → Simple.next (step simple c e) ≡ step simple   c (Simple.next e)
  {-# REWRITE here/step next/step #-}

  {-# TERMINATING #-}
  every : cmp simple
  Simple.here every = step (F unit) 1 (ret triv)
  Simple.next every = step simple 1 every

  {-# TERMINATING #-}
  alternating : cmp (Π bool λ _ → simple)
  Simple.here (alternating false) = step (F unit) 1 (ret triv)
  Simple.next (alternating false) = step simple 2 (alternating true)
  Simple.here (alternating true) = ret triv
  Simple.next (alternating true) = alternating false

  record _≈_ (s₁ s₂ : cmp simple) : Set where
    coinductive
    field
      here : Simple.here s₁ ≡ Simple.here s₂
      next : Simple.next s₁ ≈ Simple.next s₂

  ≈-cong : (c : cmp cost) {x y : Simple} → x ≈ y → step simple c x ≈ step simple c y
  _≈_.here (≈-cong c h) = Eq.cong (step (F unit) c) (_≈_.here h)
  _≈_.next (≈-cong c h) = ≈-cong c (_≈_.next h)

  Φ : val bool → ℂ
  Φ false = 0
  Φ true  = 1

  {-# TERMINATING #-}
  every≈alternating : ∀ b → every ≈ step simple (Φ b) (alternating b)
  _≈_.here (every≈alternating false) = refl
  _≈_.here (every≈alternating true) = refl
  _≈_.next (every≈alternating false) = ≈-cong 1 (every≈alternating true)
  _≈_.next (every≈alternating true) = ≈-cong 1 (every≈alternating false)


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
  Queue.enqueue (list-queue {E} l) a = step (queue E (F unit)) (length l) (list-queue (l ++ [ a ]))
  Queue.dequeue (list-queue []) = ret (nothing , list-queue [])
  Queue.dequeue (list-queue (a ∷ l)) = ret (just a , list-queue l)

  {-# TERMINATING #-}
  SPEC/list-queue : cmp (Π (list E) λ _ → queue E (F unit))
  Queue.enqueue (SPEC/list-queue {E} l) a = step (queue E (F unit)) 1 (SPEC/list-queue (l ++ [ a ]))
  Queue.dequeue (SPEC/list-queue []) = ret (nothing , SPEC/list-queue [])
  Queue.dequeue (SPEC/list-queue (a ∷ l)) = ret (just a , SPEC/list-queue l)
  Queue.quit (SPEC/list-queue l) = ret triv

  Φ : val (list E) → val (list E) → ℂ
  Φ bl fl = length bl

  {-# TERMINATING #-}
  batched-queue : cmp (Π (list E) λ _ → Π (list E) λ _ → queue E (F unit))
  Queue.quit (batched-queue {E} bl fl) = step (F unit) (Φ {E} bl fl) (ret triv)
  Queue.enqueue (batched-queue bl fl) a = batched-queue (a ∷ bl) fl
  Queue.dequeue (batched-queue {E} bl []) with reverse bl
  ... | [] = ret (nothing , batched-queue [] [])
  ... | a ∷ fl = step (F (prod⁺ (maybe E) (U (queue E (F unit))))) (length bl) (ret (just a , batched-queue [] fl))
  Queue.dequeue (batched-queue bl (a ∷ fl)) = ret (just a , batched-queue bl fl)

  {-# TERMINATING #-}
  SPEC/batched-queue : cmp (Π (list E) λ _ → Π (list E) λ _ → queue E (F unit))
  Queue.quit (SPEC/batched-queue bl fl) = ret triv
  Queue.enqueue (SPEC/batched-queue {E} bl fl) a = step (queue E (F unit)) 1 (SPEC/batched-queue (a ∷ bl) fl)
  Queue.dequeue (SPEC/batched-queue bl []) with reverse bl
  ... | [] = ret (nothing , SPEC/batched-queue [] [])
  ... | a ∷ fl = ret (just a , SPEC/batched-queue [] fl)
  Queue.dequeue (SPEC/batched-queue bl (a ∷ fl)) = ret (just a , SPEC/batched-queue bl fl)

  record _≈_ {E : tp pos} {X : tp neg} (q₁ q₂ : cmp (queue E X)) : Set where
    coinductive
    field
      quit    : Queue.quit q₁ ≡ Queue.quit q₂
      enqueue : cmp (Π E λ a → meta (Queue.enqueue q₁ a ≈ Queue.enqueue q₂ a))
      dequeue :
        Σ ℂ λ c₁ → Σ (val (maybe E)) λ a₁ → Σ (cmp (queue E X)) λ q₁' → Queue.dequeue q₁ ≡ step (F (prod⁺ (maybe E) (U (queue E X)))) c₁ (ret (a₁ , q₁')) ×
        Σ ℂ λ c₂ → Σ (val (maybe E)) λ a₂ → Σ (cmp (queue E X)) λ q₂' → Queue.dequeue q₂ ≡ step (F (prod⁺ (maybe E) (U (queue E X)))) c₂ (ret (a₂ , q₂')) ×
        -- (c₁ ≡ c₂) ×  -- not amortized
        (a₁ ≡ a₂) ×
        -- (q₁' ≈ q₂')  -- not amortized
        (step (queue E X) c₁ q₁' ≈ step (queue E X) c₂ q₂')

  ≈-cong : (c : cmp cost) {x y : Queue E X} → x ≈ y → step (queue E X) c x ≈ step (queue E X) c y
  _≈_.enqueue (≈-cong c {x} {y} h) a = ≈-cong c (_≈_.enqueue h a)
  _≈_.dequeue (≈-cong {E} {X} c h) =
    let (c₁ , a₁ , q₁' , h₁ , c₂ , a₂ , q₂' , h₂ , ha , hq') = _≈_.dequeue h in
    c + c₁ , a₁ , q₁' , Eq.cong (step (F (prod⁺ (maybe E) (U (queue E X)))) c) h₁ ,
    c + c₂ , a₂ , q₂' , Eq.cong (step (F (prod⁺ (maybe E) (U (queue E X)))) c) h₂ ,
    ha , ≈-cong c hq'
  _≈_.quit (≈-cong {X = X} c h) = Eq.cong (step X c) (_≈_.quit h)

  {-# TERMINATING #-}
  batched-queue≈SPEC/batched-queue : (bl fl : val (list E)) →
    batched-queue bl fl ≈ step (queue E (F unit)) (Φ {E} bl fl) (SPEC/batched-queue bl fl)
  _≈_.quit (batched-queue≈SPEC/batched-queue bl fl) = refl
  _≈_.enqueue (batched-queue≈SPEC/batched-queue {E} bl fl) a =
    Eq.subst
      (λ c → batched-queue (a ∷ bl) fl ≈ step (queue E (F unit)) c (SPEC/batched-queue (a ∷ bl) fl))
      (Nat.+-comm 1 (length bl))
      (batched-queue≈SPEC/batched-queue (a ∷ bl) fl)
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  ... | [] | h with h refl
  ... | refl =
    zero , nothing , batched-queue [] [] , refl ,
    zero , nothing , SPEC/batched-queue [] [] , refl ,
    refl , batched-queue≈SPEC/batched-queue [] []
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl []) | a ∷ fl | _ =
    length bl , just a , batched-queue [] fl , refl ,
    length bl , just a , SPEC/batched-queue [] fl , refl ,
    refl , ≈-cong (length bl) (batched-queue≈SPEC/batched-queue [] fl)
  _≈_.dequeue (batched-queue≈SPEC/batched-queue bl (a ∷ fl)) =
    zero , just a , batched-queue bl fl , refl ,
    length bl , just a , SPEC/batched-queue bl fl , refl ,
    refl , batched-queue≈SPEC/batched-queue bl fl

  {-# TERMINATING #-}
  batched-queue≈SPEC/list-queue : (bl fl : val (list E)) →
    batched-queue bl fl ≈ step (queue E (F unit)) (Φ {E} bl fl) (SPEC/list-queue (fl ++ reverse bl))
  _≈_.quit (batched-queue≈SPEC/list-queue bl fl) = refl
  _≈_.enqueue (batched-queue≈SPEC/list-queue {E} bl fl) a =
    Eq.subst₂
      (λ c l → batched-queue (a ∷ bl) fl ≈ step (queue E (F unit)) c (SPEC/list-queue l))
      (Nat.+-comm 1 (length bl))
      (let open ≡-Reasoning in
      begin
        fl ++ reverse (a ∷ bl)
      ≡⟨ Eq.cong (fl ++_) (List.unfold-reverse a bl) ⟩
        fl ++ reverse bl ∷ʳ a
      ≡˘⟨ List.++-assoc fl (reverse bl) [ a ] ⟩
        (fl ++ reverse bl) ∷ʳ a
      ∎)
      (batched-queue≈SPEC/list-queue (a ∷ bl) fl)
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl []) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  ... | [] | h with h refl
  ... | refl =
    zero , nothing , batched-queue [] [] , refl ,
    zero , nothing , SPEC/list-queue [] , refl ,
    refl , batched-queue≈SPEC/list-queue [] []
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl []) | a ∷ fl | _ =
    length bl , just a , batched-queue [] fl , refl ,
    length bl , just a , SPEC/list-queue fl , refl ,
    refl ,
    ≈-cong (length bl)
      ( Eq.subst
          (λ l → batched-queue [] fl ≈ SPEC/list-queue l)
          (List.++-identityʳ fl)
          (batched-queue≈SPEC/list-queue [] fl)
      )
  _≈_.dequeue (batched-queue≈SPEC/list-queue bl (a ∷ fl)) =
    zero , just a , batched-queue bl fl , refl ,
    length bl , just a , SPEC/list-queue (fl ++ reverse bl) , refl ,
    refl , batched-queue≈SPEC/list-queue bl fl


  {-# TERMINATING #-}
  ◯[list-queue≈batched-queue] : (bl fl : val (list E)) → ◯ (list-queue {E} (fl ++ reverse bl) ≈ batched-queue bl fl)
  _≈_.quit (◯[list-queue≈batched-queue] bl fl u) = Eq.sym (step/ext (F unit) (ret triv) (length bl) u)
  _≈_.enqueue (◯[list-queue≈batched-queue] {E} bl fl u) a =
    Eq.subst
      (_≈ Queue.enqueue (batched-queue bl fl) a)
      (Eq.sym (step/ext (queue E (F unit)) (list-queue _) (length (fl ++ reverse bl)) u))
      (Eq.subst
        (λ l → list-queue l ≈ batched-queue (a ∷ bl) fl)
        {x = fl ++ reverse (a ∷ bl)}
        (let open ≡-Reasoning in
        begin
          fl ++ reverse (a ∷ bl)
        ≡⟨ Eq.cong (fl ++_) (List.unfold-reverse a bl) ⟩
          fl ++ reverse bl ∷ʳ a
        ≡˘⟨ List.++-assoc fl (reverse bl) [ a ] ⟩
          (fl ++ reverse bl) ∷ʳ a
        ∎)
        (◯[list-queue≈batched-queue] {E} (a ∷ bl) fl u))
  _≈_.dequeue (◯[list-queue≈batched-queue] bl [] u) with reverse bl | List.reverse-injective {xs = bl} {ys = []}
  ... | [] | h with h refl
  ... | refl =
    zero , nothing , list-queue [] , refl ,
    zero , nothing , batched-queue [] [] , refl ,
    refl , ◯[list-queue≈batched-queue] [] [] u
  _≈_.dequeue (◯[list-queue≈batched-queue] {E} bl [] u) | a ∷ fl | _ =
    zero , just a , list-queue (fl ++ reverse []) , Eq.cong (λ l → ret (just a , list-queue l)) (Eq.sym (List.++-identityʳ fl)) ,
    zero , just a , batched-queue [] fl , step/ext (F (prod⁺ (maybe E) (U (queue E (F unit))))) _ (length bl) u ,
    refl , ◯[list-queue≈batched-queue] [] fl u
  _≈_.dequeue (◯[list-queue≈batched-queue] bl (a ∷ fl) u) =
    zero , just a , list-queue (fl ++ reverse bl) , refl ,
    zero , just a , batched-queue bl fl , refl ,
    refl , ◯[list-queue≈batched-queue] bl fl u

  -- {-# TERMINATING #-}
  -- fake-queue : cmp (queue E (F unit))
  -- Queue.quit fake-queue = ret triv
  -- Queue.enqueue fake-queue a = fake-queue
  -- Queue.dequeue fake-queue = ret (nothing , fake-queue)

  -- issue : (c₁ c₂ : ℂ) → step (queue E (F unit)) c₁ fake-queue ≈ step (queue E (F unit)) c₂ fake-queue
  -- _≈_.quit (issue c₁ c₂) = {!   !}
  -- _≈_.enqueue (issue c₁ c₂) a = issue c₁ c₂
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
  ψ (enqueue a p) q = ψ p (Queue.enqueue q a)
  ψ {A = A} (dequeue f) q =
    bind (F A) (Queue.dequeue q) λ (a , q') →
    bind (F A) (f a) λ p' →
    ψ p' q'

  step-ψ : ∀ c p q → step (F A) c (ψ p q) ≡ ψ p (step (queue E (F unit)) c q)
  step-ψ c (return x) q = refl
  step-ψ c (enqueue a p) q = step-ψ c p (Queue.enqueue q a)
  step-ψ c (dequeue f) q = refl

  postulate
    writer : (e : cmp (F E)) →
      Σ ℂ λ c → Σ (val E) λ v → e ≡ step (F E) c (ret v)
    step-ret-injective : (c₁ c₂ : ℂ) (v₁ v₂ : val E) →
      step (F E) c₁ (ret v₁) ≡ step (F E) c₂ (ret v₂) → v₁ ≡ v₂
    bind/step/commutative : ∀ {c e f} →
      bind {A = A} (F E) e (step (F E) c ∘ f) ≡ step (F E) c (bind (F E) e f)

  {-# TERMINATING #-}
  big-theorem : (q₁ q₂ : cmp (queue E (F unit))) →
    q₁ ≈ q₂ ⇔ (∀ A → (p : val (queue-program E A)) → ψ p q₁ ≡ ψ p q₂)
  big-theorem {E} q₁ q₂ = record
    { f = forward q₁ q₂
    ; g = backward q₁ q₂
    ; cong₁ = Eq.cong (forward q₁ q₂)
    ; cong₂ = Eq.cong (backward q₁ q₂)
    }
    where
      forward : (q₁ q₂ : cmp (queue E (F unit))) →
        q₁ ≈ q₂ → (∀ A → (p : val (queue-program E A)) → ψ p q₁ ≡ ψ p q₂)
      forward q₁ q₂ h A (return x) =
        Eq.cong (λ e → bind (F A) e (λ _ → ret x)) (_≈_.quit h)
      forward q₁ q₂ h A (enqueue a p) = forward (Queue.enqueue q₁ a) (Queue.enqueue q₂ a) (_≈_.enqueue h a) A p
      forward q₁ q₂ h A (dequeue f) with _≈_.dequeue h
      ... | c₁ , a , q₁' , h₁ , c₂ , _ , q₂' , h₂ , refl , hq' =
        let open ≡-Reasoning in
        begin
          (bind (F A) (Queue.dequeue q₁) λ (a , q₁') →
          bind (F A) (f a) λ p' →
          ψ p' q₁')
        ≡⟨ Eq.cong (λ e → bind (F A) e λ (a , q₁') → bind (F A) (f a) λ p' → ψ p' q₁') h₁ ⟩
          (bind (F A) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₁ (ret (a , q₁'))) λ (a , q₁') →
          bind (F A) (f a) λ p' →
          ψ p' q₁')
        ≡⟨⟩
          step (F A) c₁ (
          bind (F A) (f a) λ p' →
          ψ p' q₁')
        ≡˘⟨ bind/step/commutative {E = A} {c = c₁} {e = f a} ⟩
          (bind (F A) (f a) λ p' →
          step (F A) c₁ (ψ p' q₁'))
        ≡⟨
          Eq.cong (bind (F A) (f a)) (funext λ p' →
          begin
            step (F A) c₁ (ψ p' q₁')
          ≡⟨ step-ψ c₁ p' q₁' ⟩
            ψ p' (step (queue E (F unit)) c₁ q₁')
          ≡⟨ forward (step (queue E (F unit)) c₁ q₁') (step (queue E (F unit)) c₂ q₂') hq' A p' ⟩
            ψ p' (step (queue E (F unit)) c₂ q₂')
          ≡˘⟨ step-ψ c₂ p' q₂' ⟩
            step (F A) c₂ (ψ p' q₂')
          ∎)
        ⟩
          (bind (F A) (f a) λ p' →
          step (F A) c₂ (ψ p' q₂'))
        ≡⟨ bind/step/commutative {E = A} {c = c₂} {e = f a} ⟩
          step (F A) c₂ (
          bind (F A) (f a) λ p' →
          ψ p' q₂')
        ≡⟨⟩
          (bind (F A) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₂ (ret (a , q₂'))) λ (a , q₂') →
          bind (F A) (f a) λ p' →
          ψ p' q₂')
        ≡˘⟨ Eq.cong (λ e → bind (F A) e λ (a , q₂') → bind (F A) (f a) λ p' → ψ p' q₂') h₂ ⟩
          (bind (F A) (Queue.dequeue q₂) λ (a , q₂') →
          bind (F A) (f a) λ p' →
          ψ p' q₂')
        ∎

      backward : (q₁ q₂ : cmp (queue E (F unit))) →
        (∀ A → (p : val (queue-program E A)) → ψ p q₁ ≡ ψ p q₂) → q₁ ≈ q₂
      _≈_.quit (backward q₁ q₂ typical) = typical unit (return triv)
      _≈_.enqueue (backward q₁ q₂ typical) a =
        backward (Queue.enqueue q₁ a) (Queue.enqueue q₂ a) (λ A p → typical A (enqueue a p))
      _≈_.dequeue (backward q₁ q₂ typical) =
        let (c₁ , (a₁ , q₁') , h₁) = writer (Queue.dequeue q₁) in
        let (c₂ , (a₂ , q₂') , h₂) = writer (Queue.dequeue q₂) in
        c₁ , a₁ , q₁' , h₁ ,
        c₂ , a₂ , q₂' , h₂ ,
        ( let (c₁' , triv , h₁') = writer (Queue.quit q₁') in
          let (c₂' , triv , h₂') = writer (Queue.quit q₂') in
          step-ret-injective
            (c₁ + c₁')
            (c₂ + c₂')
            a₁
            a₂
            (let open ≡-Reasoning in
            begin
              step (F (maybe E)) (c₁ + c₁') (ret a₁)
            ≡⟨⟩
              step (F (maybe E)) c₁ (
              bind (F (maybe E)) (step (F unit) c₁' (ret triv)) λ _ →
              ret a₁)
            ≡˘⟨ Eq.cong (λ e → step (F (maybe E)) c₁ (bind (F (maybe E)) e λ _ → ret a₁)) h₁' ⟩
              step (F (maybe E)) c₁ (
              bind (F (maybe E)) (Queue.quit q₁') λ _ →
              ret a₁)
            ≡⟨⟩
              step (F (maybe E)) c₁ (ψ (return a₁) q₁')
            ≡⟨⟩
              (bind (F (maybe E)) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₁ (ret (a₁ , q₁'))) λ (a , q₁') →
              bind {A = queue-program E (maybe E)} (F (maybe E)) (ret (return a)) λ p' →
              ψ p' q₁')
            ≡˘⟨ Eq.cong (λ e → bind (F (maybe E)) e _) h₁ ⟩
              (bind (F (maybe E)) (Queue.dequeue q₁) λ (a , q₁') →
              bind {A = queue-program E (maybe E)} (F (maybe E)) (ret (return a)) λ p' →
              ψ p' q₁')
            ≡⟨⟩
              ψ (dequeue (λ a → ret (return a))) q₁
            ≡⟨ typical (maybe E) (dequeue (λ a → ret (return a))) ⟩
              ψ (dequeue (λ a → ret (return a))) q₂
            ≡⟨⟩
              (bind (F (maybe E)) (Queue.dequeue q₂) λ (a , q₂') →
              bind {A = queue-program E (maybe E)} (F (maybe E)) (ret (return a)) λ p' →
              ψ p' q₂')
            ≡⟨ Eq.cong (λ e → bind (F (maybe E)) e _) h₂ ⟩
              (bind (F (maybe E)) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₂ (ret (a₂ , q₂'))) λ (a , q₂') →
              bind {A = queue-program E (maybe E)} (F (maybe E)) (ret (return a)) λ p' →
              ψ p' q₂')
            ≡⟨⟩
              step (F (maybe E)) c₂ (ψ (return a₂) q₂')
            ≡⟨⟩
              step (F (maybe E)) c₂ (
              bind (F (maybe E)) (Queue.quit q₂') λ _ →
              ret a₂)
            ≡⟨ Eq.cong (λ e → step (F (maybe E)) c₂ (bind (F (maybe E)) e λ _ → ret a₂)) h₂' ⟩
              step (F (maybe E)) c₂ (
              bind (F (maybe E)) (step (F unit) c₂' (ret triv)) λ _ →
              ret a₂)
            ≡⟨⟩
              step (F (maybe E)) (c₂ + c₂') (ret a₂)
            ∎)
        ) ,
        backward
          (step (queue E (F unit)) c₁ q₁')
          (step (queue E (F unit)) c₂ q₂')
          λ A p' →
            let open ≡-Reasoning in
            begin
              ψ p' (step (queue E (F unit)) c₁ q₁')
            ≡˘⟨ step-ψ c₁ p' q₁' ⟩
              step (F A) c₁ (ψ p' q₁')
            ≡⟨⟩
              (bind (F A) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₁ (ret (a₁ , q₁'))) λ (a , q₁') →
              bind {A = queue-program E A} (F A) (ret p') λ p' →
              ψ p' q₁')
            ≡˘⟨ Eq.cong (λ e → bind (F A) e _) h₁ ⟩
              (bind (F A) (Queue.dequeue q₁) λ (a , q₁') →
              bind {A = queue-program E A} (F A) (ret p') λ p' →
              ψ p' q₁')
            ≡⟨⟩
              ψ (dequeue (const (ret p'))) q₁
            ≡⟨ typical A (dequeue (const (ret p'))) ⟩
              ψ (dequeue (const (ret p'))) q₂
            ≡⟨⟩
              (bind (F A) (Queue.dequeue q₂) λ (a , q₂') →
              bind {A = queue-program E A} (F A) (ret p') λ p' →
              ψ p' q₂')
            ≡⟨ Eq.cong (λ e → bind (F A) e _) h₂ ⟩
              (bind (F A) (step (F (prod⁺ (maybe E) (U (queue E (F unit))))) c₂ (ret (a₂ , q₂'))) λ (a , q₂') →
              bind {A = queue-program E A} (F A) (ret p') λ p' →
              ψ p' q₂')
            ≡⟨⟩
              step (F A) c₂ (ψ p' q₂')
            ≡⟨ step-ψ c₂ p' q₂' ⟩
              ψ p' (step (queue E (F unit)) c₂ q₂')
            ∎


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
