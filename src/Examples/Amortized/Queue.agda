{-# OPTIONS --rewriting #-}

module Examples.Amortized.Queue where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Data.Product
open import Calf.Data.Maybe
open import Calf.Data.Nat as Nat using (ℕ; zero; suc; nat; _+_; _∸_; pred; _*_; _^_; _>_)
import Data.Nat.Properties as Nat
open import Calf.Data.List
import Data.List.Properties as List
open import Calf.Data.Equality as Eq using (_≡_; refl; _≡⁺_; ≡⁺-syntax; _≡⁻_; ≡⁻-syntax; module ≡-Reasoning)
open import Function hiding (_⇔_)

open import Examples.Amortized.Core


-- moving `E` to a parameter on `module Queue` breaks things - Agda bug?
E : tp⁺
E = nat

postulate
  queue : tp⁻ → tp⁻
record Queue (X : tp⁻) : Set where
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

postulate
  _≈⁻_ : (q₁ q₂ : cmp (queue X)) → tp⁻
record _≈_ (q₁ q₂ : cmp (queue X)) : Set where
  coinductive
  field
    quit    : cmp $
      Queue.quit q₁ ≡⁻[ X ] Queue.quit q₂
    enqueue : cmp $
      Π E λ e → Queue.enqueue q₁ e ≈⁻ Queue.enqueue q₂ e
    dequeue : cmp $
      (proj₁ (Queue.dequeue q₁) ≡⁺[ maybe E ] proj₁ (Queue.dequeue q₂)) ⋉
      (proj₂ (Queue.dequeue q₁) ≈⁻ proj₂ (Queue.dequeue q₂))
postulate
  ≈⁻/decode : {q₁ q₂ : cmp (queue X)} → val (U (q₁ ≈⁻ q₂)) ≡ q₁ ≈ q₂
  {-# REWRITE ≈⁻/decode #-}


{-# TERMINATING #-}
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


data QueueProgram (A : tp⁺) : Set
queue-program : tp⁺ → tp⁺
queue-program A = meta⁺ (QueueProgram A)
data QueueProgram A where
  return  : val A → QueueProgram A
  enqueue : val E → val (queue-program A) → QueueProgram A
  dequeue : val (U (Π (maybe E) λ _ → F (queue-program A))) → QueueProgram A

{-# TERMINATING #-}
ψ : cmp (Π (queue-program A) λ _ → Π (U (queue X)) λ _ → A ⋉ X)
ψ {A} {X} (return a   ) q = a , Queue.quit q
ψ {A} {X} (enqueue e p) q = ψ p (Queue.enqueue q e)
ψ {A} {X} (dequeue k  ) q =
  bind (A ⋉ X) (k (proj₁ (Queue.dequeue q))) λ p →
  ψ p (proj₂ (Queue.dequeue q))

postulate
  _≈'_ : (q₁ q₂ : cmp (queue X)) → tp⁻
  ≈'/decode : ∀ {q₁ q₂ : cmp (queue X)} →
    val (U (q₁ ≈' q₂)) ≡ ((A : tp⁺) → cmp (Π (queue-program A) λ p → ψ p q₁ ≡⁻[ A ⋉ X ] ψ p q₂))
  {-# REWRITE ≈'/decode #-}

{-# TERMINATING #-}
classic-amortization : {q₁ q₂ : cmp (queue X)} → val (U (q₁ ≈⁻ q₂) ⇔ U (q₁ ≈' q₂))
classic-amortization {X} = forward , backward
  where
    forward : {q₁ q₂ : cmp (queue X)} → q₁ ≈ q₂ → cmp (q₁ ≈' q₂)
    forward h A (return a   ) = Eq.cong (a ,_) (_≈_.quit h)
    forward h A (enqueue e p) = forward (_≈_.enqueue h e) A p
    forward h A (dequeue k  ) =
      Eq.cong₂
        (λ e₁ e₂ → bind (A ⋉ X) (k e₁) e₂)
        (proj₁ (_≈_.dequeue h))
        (funext (forward (proj₂ (_≈_.dequeue h)) A))

    backward : {q₁ q₂ : cmp (queue X)} → cmp (q₁ ≈' q₂) → q₁ ≈ q₂
    _≈_.quit (backward classic) = Eq.cong proj₂ (classic unit (return triv))
    _≈_.enqueue (backward classic) e = backward λ A p → classic A (enqueue e p)
    _≈_.dequeue (backward classic) =
      Eq.cong proj₁ (classic (maybe E) (dequeue λ e → ret (return e))) ,
      backward λ A p → classic A (dequeue λ _ → ret p)
