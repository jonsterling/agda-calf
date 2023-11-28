# Treap

In this file, we implement and verify the [treap](https://en.wikipedia.org/wiki/Treap) data structure.

<!--
```agda
{-# OPTIONS --prop --rewriting #-}
```
-->

First, let's import some stuff:
```agda
module Examples.Sequence.Treap where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid
import Data.Rational as ℚ

open import Calf costMonoid
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid

open import Data.Interval
open import Data.Bool.Base
open import Data.List.Properties
open import Data.Nat.Properties as NatProp
open import Examples.Decalf.ProbabilisticChoice


open import Calf.Data.Product
open import Calf.Data.Nat as Nat using (zero; suc; >-nonZero) 
open import Calf.Data.List


open import Function using (_$_)

open import Relation.Nullary
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)
```

Here is the definition of treap:
```agda
data ITreap (A : tp⁺) : val (list A) → Set where
  leaf : ITreap A []
  node : {l₁ l₂ : val (list A)}
    (t₁ : ITreap A l₁) (a : val A) (t₂ : ITreap A l₂)
    → ITreap A (l₁ ++ [ a ] ++ l₂)
itreap : (A : tp⁺) → val (list A) → tp⁺
itreap A l = meta⁺ (ITreap A l)
```

Here is the implementation of join:
```agda
nz-lemma : {T : Set} → (a₁ a₂ : T) → (l₁₁ l₁₂ l₂₁ l₂₂ : List T) → Nat.zero Nat.< (length (l₁₁ ++ [ a₁ ] ++ l₁₂) Nat.+ length (l₂₁ ++ [ a₂ ] ++ l₂₂))
nz-lemma a₁ a₂ l₁₁ l₁₂ l₂₁ l₂₂ =
  let open NatProp.≤-Reasoning in
  begin
    length [ a₁ ] 
  ≤⟨ m≤n+m (length [ a₁ ]) (length l₁₁) ⟩
    (length l₁₁) Nat.+ (length [ a₁ ])
  ≡˘⟨ length-++ l₁₁ ⟩
    length (l₁₁ ++ [ a₁ ])
  ≤⟨ m≤m+n (length (l₁₁ ++ [ a₁ ])) _ ⟩
    length (l₁₁ ++ [ a₁ ]) Nat.+ (length l₁₂) 
  ≡˘⟨ length-++ (l₁₁ ++ [ a₁ ]) ⟩
    length ((l₁₁ ++ [ a₁ ]) ++ l₁₂)
  ≡⟨ Eq.cong length (++-assoc l₁₁ _ _) ⟩
    length (l₁₁ ++ [ a₁ ] ++ l₁₂)
  ≤⟨ m≤m+n (length (l₁₁ ++ [ a₁ ] ++ l₁₂)) _ ⟩
    ((length (l₁₁ ++ [ a₁ ] ++ l₁₂) Nat.+ length (l₂₁ ++ [ a₂ ] ++ l₂₂)))
  ∎ 

i-join :
  cmp $
    Π (list A) λ l₁ → Π (itreap A l₁) λ _ →
    Π A λ a →
    Π (list A) λ l₂ → Π (itreap A l₂) λ _ →
    F (Σ⁺ (list A) λ l →
      (meta⁺ (l ≡ l₁ ++ (a ∷ l₂))) ×⁺ (itreap A l))
i-join .[] leaf a .[] leaf = ret ([ a ] , refl , node leaf a leaf)
i-join .[] leaf a l₂ t₂@(node t₂₁ a₂ t₂₂) =
  flip (F _) (1 / suc (length l₂))
    (step (F _) (1) (bind (F _) (i-join _ leaf a _ t₂₁) λ (l' , h' , t') →
      ret (l' ++ [ a₂ ] ++ _ , Eq.cong (_++ a₂ ∷ _) h' , node t' a₂ t₂₂)))
    (ret ([ a ] ++ l₂ , refl , node leaf a t₂)) 
i-join l₁ t₁@(node {l₁₁} {l₁₂} t₁₁  a₁ t₁₂) a .[] leaf = 
  flip (F _) ((1 / suc (length l₁))) 
    (step (F _) (1) (bind (F _) (i-join l₁₂ t₁₂ a [] leaf) λ (l' , h' , t') →  
      ret (_ ++ (a₁ ∷ l') , Eq.trans (Eq.cong (λ l'' → l₁₁ ++ (a₁ ∷ l'')) h') (Eq.sym (++-assoc _ (a₁ ∷ _) [ a ])) ,  node t₁₁ a₁ t')))
    (ret ( l₁ ++ [ a ] , refl , node t₁ a leaf))
i-join l₁ t₁@(node {l₁₁} {l₁₂} t₁₁ a₁ t₁₂) a l₂ t₂@(node {l₂₁} {l₂₂} t₂₁ a₂ t₂₂) = 
  flip (F _) (1 / suc (length l₁ Nat.+ length l₂)) 
    (flip (F _) (_/_ (length l₁) (length l₁ Nat.+ length l₂) {{ Nat.>-nonZero (nz-lemma a₁ a₂ l₁₁ l₁₂ l₂₁ l₂₂)}} {{m≤m+n _ _}})
      -- joining into the right subtree
      (step (F _) (1) (bind (F _) (i-join _ t₁ a _ t₂₁) λ (l' , h' , t') → ret ( l' ++ (a₂ ∷ l₂₂) , Eq.trans (Eq.cong (λ l' → l' ++ a₂ ∷ l₂₂) h') (++-assoc (l₁₁ ++ [ a₁ ] ++ l₁₂)  ([ a ] ++ l₂₁) ([ a₂ ] ++ l₂₂)) , node t' a₂ t₂₂ )))
      -- joining into the left subtree
      (step (F _) (1) (bind (F _) (i-join _ t₁₂ a _ t₂) λ (l' , h' , t') → ret ( l₁₁ ++ (a₁ ∷ l') , Eq.trans (Eq.cong (λ l' → l₁₁ ++ a₁ ∷ l') h') (Eq.sym (++-assoc l₁₁ (a₁ ∷ l₁₂) _))  , node t₁₁ a₁ t' ))))
    -- the added element has the highest priority
    (ret (l₁ ++ (a ∷ l₂) , refl , node t₁ a t₂)) 


i-join/cost : (l₁ l₂ : val (list A)) → (t₁ : val (itreap A l₁)) → (t₂ : val (itreap A l₂)) → ℂ
i-join/cost l₁ l₂ t₁ t₂ =  (length l₁) Nat.⊔ (length l₂)

max-lemma : (x : Nat.ℕ) → x ≡ x Nat.⊔ 0
max-lemma 0 = refl
max-lemma (suc x) = refl

-- bind-lemma : (e : cmp (F A)) → (f : val A → cmp (F A)) → (bind (F unit) (bind (F A) e f) (λ _ → ret triv)) ≡ bind (F unit) e (λ _ → ret triv)
-- bind-lemma {A} e f = {!   !}

i-join/is-bounded : ∀  l₁ t₁ a l₂ t₂ → 
  IsBounded (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (itreap A l)) (i-join l₁ t₁ a l₂ t₂) (i-join/cost l₁ l₂ t₁ t₂)
i-join/is-bounded .[] leaf a .[]  leaf = step⋆-mono-≤⁻ {0} {0} Nat.z≤n 
i-join/is-bounded {A} l₁ t₁@(node {l₁₁} {l₁₂} t₁₁ a₁ t₁₂) a l₂@.[] leaf =
    let open ≤⁻-Reasoning cost in
    begin
      flip (F unit) ((1 / suc (length l₁))) (
        step (F unit) (1) (
          bind (F unit)
            (bind (F (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ (a ∷ l₂))) ×⁺ (itreap A l))) (i-join l₁₂ t₁₂ a [] leaf) 
            λ (l' , h' , t') →  
              ret (_ ++ (a₁ ∷ l') , Eq.trans (Eq.cong (λ l'' → l₁₁ ++ (a₁ ∷ l'')) h') (Eq.sym (++-assoc _ (a₁ ∷ _) [ a ])) ,  node t₁₁ a₁ t'))
          (λ _ → ret triv)
        )
      )
      (ret triv)
    ≤⟨ ≤⁻-mono {F unit} (flip (F unit) _ _) (step-monoˡ-≤⁻ (ret triv) (Nat.z≤n {1})) ⟩ 
      flip (F unit) ((1 / suc (length l₁))) (
        step (F unit) (1) (
          bind (F unit)
            (bind (F (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ (a ∷ l₂))) ×⁺ (itreap A l))) (i-join l₁₂ t₁₂ a [] leaf) 
            λ (l' , h' , t') →  
              ret (_ ++ (a₁ ∷ l') , Eq.trans (Eq.cong (λ l'' → l₁₁ ++ (a₁ ∷ l'')) h') (Eq.sym (++-assoc _ (a₁ ∷ _) [ a ])) ,  node t₁₁ a₁ t'))
          (λ _ → ret triv)
        )
      )
      (step (F unit) 1 (ret triv))
    ≡˘⟨ step/flip {c = 1} ⟩ 
      step (F unit) (1) (
        flip (F unit) (1 / suc (length l₁)) (
          (bind (F unit)
            (bind (F (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ (a ∷ l₂))) ×⁺ (itreap A l))) (i-join l₁₂ t₁₂ a [] leaf) 
              λ (l' , h' , t') →  
                ret (_ ++ (a₁ ∷ l') , Eq.trans (Eq.cong (λ l'' → l₁₁ ++ (a₁ ∷ l'')) h') (Eq.sym (++-assoc _ (a₁ ∷ _) [ a ])) ,  node t₁₁ a₁ t'))
            (λ _ → ret triv)
          )
        )
        (ret triv)
      )
    ≡⟨ Eq.cong (λ x → step (F unit) (1) (flip (F unit) (1 / suc (length l₁)) x (ret triv))) refl ⟩
      step (F unit) (1) (
        flip (F unit) (1 / suc (length l₁)) (
          (bind (F unit)
            (i-join l₁₂ t₁₂ a [] leaf) 
            (λ _ → ret triv)
          )
        )
        (ret triv)
      )
    ≤⟨ ≤⁻-mono {F unit} (λ x → step (F unit) 1 (flip (F unit) (1 / suc (length (l₁₁ ++ [ a₁ ] ++ l₁₂))) x (ret triv))) (i-join/is-bounded l₁₂ t₁₂ a [] leaf) ⟩
      step (F unit) (1) (
        flip (F unit) (1 / suc (length l₁)) 
          (step⋆ (i-join/cost l₁₂ [] t₁₂ leaf))
          (ret triv)
        )
    ≡⟨ Eq.cong (λ x → step (F unit) (1) (flip (F unit) (1 / suc (length l₁)) x (ret triv))) (Eq.cong step⋆ {(i-join/cost l₁₂ [] t₁₂ leaf)} {(length l₁₂)} (Eq.sym (max-lemma _))) ⟩
      step (F unit) (1) (
        flip (F unit) (1 / suc (length l₁)) 
          (step⋆ (length l₁₂))
          (ret triv)
      )
    ≤⟨ ≤⁻-mono {F unit} (λ x → step (F unit) 1 (flip (F unit) (1 / suc (length l₁)) (step⋆ (length l₁₂)) x)) (step-monoˡ-≤⁻ (ret triv) (Nat.z≤n {length l₁₂})) ⟩
      step (F unit) (1) (
        flip (F unit) (1 / suc (length l₁)) 
          (step⋆ (length l₁₂))
          (step⋆ (length l₁₂))
      )
    ≡⟨ Eq.cong (λ x → step (F unit) (1) x) (flip/same _ _) ⟩
      step⋆ (1 + length l₁₂)
    ≤⟨ step⋆-mono-≤⁻ (m≤n+m (1 + length l₁₂) (length l₁₁)) ⟩
      step⋆ ((length l₁₁) + (1 + length l₁₂))
    ≡˘⟨ Eq.cong (λ x → step⋆ ((length l₁₁) + x)) (length-++ [ a₁ ] {l₁₂}) ⟩
      step⋆ ((length l₁₁) + length([ a₁ ] ++ l₁₂))
    ≡˘⟨ Eq.cong step⋆ (length-++ l₁₁) ⟩
      step⋆ (length (l₁₁ ++ [ a₁ ] ++ l₁₂))
    ≡⟨ Eq.cong step⋆ {(length l₁)} {((length l₁) Nat.⊔ 0)} (max-lemma _) ⟩
      step⋆ (i-join/cost (l₁₁ ++ [ a₁ ] ++ l₁₂) [] (node t₁₁ a₁ t₁₂) leaf)
    ∎
i-join/is-bounded .[]  leaf a .(_ ++ [ a₁ ] ++ _) (node t₂ a₁ t₃) = {!   !}
i-join/is-bounded .(_ ++ [ a₂ ] ++ _)  (node t₁ a₂ t₄) a .(_ ++ [ a₁ ] ++ _) (node t₂ a₁ t₃) = {!   !}

```



-- # Expected Cost

-- What happens when we want to analyze expected cost?
-- Here's an idea:
-- ```agda
-- postulate
--   expectation : Ω

--   law/expectation₁ : (X : tp⁻) (p : 𝕀) (c : ℂ) (e₀ e₁ : cmp X) (v : expectation) →
--     flip X p e₀ (step X c e₁) ≡ step X (toℚ p ℚ.* c) (flip X p e₀ e₁)

-- law/expectation₀ : (X : tp⁻) (p : 𝕀) (c : ℂ) (e₀ e₁ : cmp X) (v : expectation) →
--   flip X p (step X c e₀) e₁ ≡ step X (toℚ (1- p) ℚ.* c) (flip X p e₀ e₁)
-- law/expectation₀ X p c e₀ e₁ v =
--   let open ≡-Reasoning in
--   begin
--     flip X p (step X c e₀) e₁
--   ≡⟨ flip/sym X p (step X c e₀) e₁ ⟩
--     flip X (1- p) e₁ (step X c e₀)
--   ≡⟨ law/expectation₁ X (1- p) c e₁ e₀ v ⟩
--     step X (toℚ (1- p) ℚ.* c) (flip X (1- p) e₁ e₀)
--   ≡˘⟨ Eq.cong (step X (toℚ (1- p) ℚ.* c)) (flip/sym X p e₀ e₁) ⟩
--     step X (toℚ (1- p) ℚ.* c) (flip X p e₀ e₁)
--   ∎

-- law/expectation : (X : tp⁻) (p : 𝕀) (c₀ c₁ : ℂ) (e₀ e₁ : cmp X) (v : expectation) →
--   flip X p (step X c₀ e₀) (step X c₁ e₁) ≡ step X (toℚ (1- p) ℚ.* c₀ + toℚ p ℚ.* c₁) (flip X p e₀ e₁)
-- law/expectation X p c₀ c₁ e₀ e₁ v =
--   let open ≡-Reasoning in
--   begin
--     flip X p (step X c₀ e₀) (step X c₁ e₁)
--   ≡⟨ law/expectation₀ X p c₀ e₀ (step X c₁ e₁) v ⟩
--     step X (toℚ (1- p) ℚ.* c₀) (flip X p e₀ (step X c₁ e₁))
--   ≡⟨ Eq.cong (step X (toℚ (1- p) ℚ.* c₀)) (law/expectation₁ X p c₁ e₀ e₁ v) ⟩
--     step X (toℚ (1- p) ℚ.* c₀ + toℚ p ℚ.* c₁) (flip X p e₀ e₁)
--   ∎
-- ```      
                         