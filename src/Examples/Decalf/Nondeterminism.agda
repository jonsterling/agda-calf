{-# OPTIONS --rewriting #-}

module Examples.Decalf.Nondeterminism where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ; _+_)

open import Calf costMonoid hiding (A)
open import Calf.Data.Nat as Nat using (nat; zero; suc; _*_)
import Data.Nat.Properties as Nat
open import Data.Nat.Square
open import Calf.Data.List as List using (list; []; _∷_; [_]; _++_; length)
import Data.Fin as Fin
open import Calf.Data.Bool using (bool; false; true; if_then_else_)
open import Calf.Data.Product using (unit; _×⁺_)
open import Calf.Data.Equality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.IsBounded costMonoid
open import Relation.Nullary
open import Function


postulate
  branch : (X : tp⁻) → cmp X → cmp X → cmp X
  fail : (X : tp⁻) → cmp X

  branch/idˡ : {e : cmp X} →
    branch X (fail X) e ≡ e
  branch/idʳ : {e : cmp X} →
    branch X e (fail X) ≡ e
  branch/assoc : {e₀ e₁ e₂ : cmp X} →
    branch X (branch X e₀ e₁) e₂ ≡ branch X e₀ (branch X e₁ e₂)
  branch/comm : {e₀ e₁ : cmp X} →
    branch X e₀ e₁ ≡ branch X e₁ e₀
  branch/idem : {e : cmp X} →
    branch X e e ≡ e

  branch/step : (c : ℂ) {e₀ e₁ : cmp X} →
    step X c (branch X e₀ e₁) ≡ branch X (step X c e₀) (step X c e₁)
  fail/step : (c : ℂ) →
    step X c (fail X) ≡ fail X

  bind/fail : {A : tp⁺} {f : val A → cmp X} →
    bind X (fail (F A)) f ≡ fail X
  bind/branch : {A : tp⁺} {e₀ e₁ : cmp (F A)} {f : val A → cmp X} →
    bind X (branch (F A) e₀ e₁) f ≡ branch X (bind X e₀ f) (bind X e₁ f)
  {-# REWRITE bind/fail bind/branch #-}


open import Examples.Sorting.Sequential.Comparable
module QuickSort (M : Comparable) where
  open Comparable M
  open import Examples.Sorting.Sequential.Core M

  choose : cmp $ Π (list A) λ l → F (Σ⁺ A λ pivot → Σ⁺ (list A) λ l' → meta⁺ (l ↭ pivot ∷ l'))
  choose []       = fail (F _)
  choose (x ∷ xs) =
    branch (F _)
      (bind (F _) (choose xs) λ (pivot , l , xs↭pivot∷l) → ret (pivot , x ∷ l , trans (prep x xs↭pivot∷l) (swap x pivot refl)))
      (ret (x , xs , refl))

  choose/cost : cmp $ Π (list A) λ _ → cost
  choose/cost l = ret triv

  choose/is-bounded : ∀ x xs → IsBoundedG _ (choose (x ∷ xs)) (choose/cost (x ∷ xs))
  choose/is-bounded x [] = ≤⁻-reflexive branch/idˡ
  choose/is-bounded x (x' ∷ xs) =
    let open ≤⁻-Reasoning cost in
    begin
      branch (F unit) (bind (F unit) (choose (x' ∷ xs)) λ _ → ret triv) (ret triv)
    ≲⟨ ≤⁻-mono (λ e → branch (F unit) (bind (F unit) e λ _ → ret triv) (ret triv)) (choose/is-bounded x' xs) ⟩
      branch (F unit) (ret triv) (ret triv)
    ≡⟨ branch/idem ⟩
      ret triv
    ∎

  partition : cmp $ Π A λ pivot → Π (list A) λ l → F (Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ l))
  partition pivot []       = ret ([] , [] , [] , [] , refl)
  partition pivot (x ∷ xs) =
    bind (F _) (partition pivot xs) λ (xs₁ , xs₂ , h₁ , h₂ , xs₁++xs₂↭xs) →
    bind (F _) (x ≤? pivot) $ case-≤
      (λ x≤pivot → ret (x ∷ xs₁ , xs₂ , x≤pivot ∷ h₁ , h₂ , prep x xs₁++xs₂↭xs))
      (λ x≰pivot → ret (xs₁ , x ∷ xs₂ , h₁ , ≰⇒≥ x≰pivot ∷ h₂ , trans (shift-↭ x xs₁ xs₂) (prep x xs₁++xs₂↭xs)))

  partition/cost : cmp $ Π A λ a → Π (list A) λ l → cost
  partition/cost _ l = step⋆ (length l)

  partition/is-bounded : ∀ pivot l → IsBoundedG _ (partition pivot l) (partition/cost pivot l)
  partition/is-bounded pivot []       = ≤⁻-refl
  partition/is-bounded pivot (x ∷ xs) =
    let open ≤⁻-Reasoning cost in
    begin
      ( bind (F unit) (partition pivot xs) λ (xs₁ , xs₂ , h₁ , h₂ , xs₁++xs₂↭xs) →
        bind (F unit) (x ≤? pivot) λ x≤?pivot →
        bind {Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ x ∷ xs)} (F unit)
          ( case-≤
              (λ x≤pivot → ret (x ∷ xs₁ , xs₂ , x≤pivot ∷ h₁ , h₂ , prep x xs₁++xs₂↭xs))
              (λ x≰pivot → ret (xs₁ , x ∷ xs₂ , h₁ , ≰⇒≥ x≰pivot ∷ h₂ , trans (shift-↭ x xs₁ xs₂) (prep x xs₁++xs₂↭xs)))
            x≤?pivot
          )
          (λ _ → ret triv)
      )
    ≡⟨
      ( Eq.cong (bind (F unit) (partition pivot xs)) $ funext λ (xs₁ , xs₂ , h₁ , h₂ , xs₁++xs₂↭xs) →
        Eq.cong (bind (F unit) (x ≤? pivot)) $ funext $
        bind/case-≤
          {B = Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ x ∷ xs)}
          {X = F unit}
          {f = λ _ → ret triv}
          (λ x≤pivot → ret (x ∷ xs₁ , xs₂ , x≤pivot ∷ h₁ , h₂ , prep x xs₁++xs₂↭xs))
          (λ x≰pivot → ret (xs₁ , x ∷ xs₂ , h₁ , ≰⇒≥ x≰pivot ∷ h₂ , trans (shift-↭ x xs₁ xs₂) (prep x xs₁++xs₂↭xs)))
      )
    ⟩
      ( bind (F unit) (partition pivot xs) λ _ →
        bind (F unit) (x ≤? pivot) $ case-≤
          (λ _ → ret triv)
          (λ _ → ret triv)
      )
    ≡⟨
      ( Eq.cong (bind (F unit) (partition pivot xs)) $ funext λ (xs₁ , xs₂ , h₁ , h₂ , xs₁++xs₂↭xs) →
        Eq.cong (bind (F unit) (x ≤? pivot)) $ funext $
        case-≤/idem (ret triv)
      )
    ⟩
      ( bind (F unit) (partition pivot xs) λ _ →
        bind (F unit) (x ≤? pivot) λ _ →
        ret triv
      )
    ≲⟨
      ( ≤⁻-mono
          {Π (Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ xs)) λ _ → F unit}
          (bind (F unit) (partition pivot xs)) $
        λ-mono-≤⁻ λ _ →
        h-cost x pivot
      )
    ⟩
      ( bind (F unit) (partition pivot xs) λ _ →
        step⋆ 1
      )
    ≡⟨⟩
      ( bind (F unit) (bind (F unit) (partition pivot xs) λ _ → ret triv) λ _ →
        step⋆ 1
      )
    ≲⟨ ≤⁻-mono (λ e → bind (F unit) (bind (F unit) e λ _ → ret triv) λ _ → step (F unit) 1 (ret triv)) (partition/is-bounded pivot xs) ⟩
      ( bind (F unit) (step (F unit) (length xs) (ret triv)) λ _ →
        step⋆ 1
      )
    ≡⟨⟩
      step⋆ (length xs + 1)
    ≡⟨ Eq.cong step⋆ (Nat.+-comm (length xs) 1) ⟩
      step⋆ (length (x ∷ xs))
    ∎

  {-# TERMINATING #-}
  sort : cmp $ Π (list A) λ _ → F (list A)
  sort []       = ret []
  sort (x ∷ xs) =
    bind (F _) (choose (x ∷ xs)) λ (pivot , l , x∷xs↭pivot∷l) →
    bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
    bind (F _) (sort l₁) λ l₁' →
    bind (F _) (sort l₂) λ l₂' →
    ret (l₁' ++ [ x ] ++ l₂')

  sort/cost : cmp $ Π (list A) λ _ → cost
  sort/cost l = step⋆ (length l ²)

  sort/arithmetic : (m n : val nat) → m ² + n ² Nat.≤ (m + n) ²
  sort/arithmetic m n =
    let open Nat.≤-Reasoning in
    begin
      m ² + n ²
    ≤⟨ Nat.+-mono-≤ (Nat.m≤m+n (m * m) (n * m)) (Nat.m≤n+m (n * n) (m * n)) ⟩
      (m * m + n * m) + (m * n + n * n)
    ≡˘⟨ Eq.cong₂ _+_ (Nat.*-distribʳ-+ m m n) (Nat.*-distribʳ-+ n m n) ⟩
      (m + n) * m + (m + n) * n
    ≡˘⟨ Nat.*-distribˡ-+ (m + n) m n ⟩
      (m + n) * (m + n)
    ∎

  {-# TERMINATING #-}
  sort/is-bounded : ∀ l → IsBoundedG _ (sort l) (sort/cost l)
  sort/is-bounded []       = ≤⁻-refl
  sort/is-bounded (x ∷ xs) =
    let open ≤⁻-Reasoning cost in
    begin
      ( bind (F _) (choose (x ∷ xs)) λ (pivot , l , x∷xs↭pivot∷l) →
        bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
        bind (F _) (sort l₁) λ _ →
        bind (F _) (sort l₂) λ _ →
        ret triv
      )
    ≲⟨
      ( ≤⁻-mono
          {Π (Σ⁺ A λ pivot → Σ⁺ (list A) λ l' → meta⁺ (x ∷ xs ↭ pivot ∷ l')) λ _ → F unit}
          {F unit}
          (bind (F unit) (choose (x ∷ xs)))
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
            bind (F _) (sort l₁) λ _ →
            bind (F _) (sort l₂) λ _ →
            ret triv}
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
            bind (F _) (sort l₁) λ _ →
            step⋆ (length l₂ ²)} $
        λ-mono-≤⁻ λ (pivot , l , x∷xs↭pivot∷l) →
        ≤⁻-mono
          {Π (Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ l)) λ _ → F unit}
          {F unit}
          (bind (F unit) (partition pivot l)) $
        λ-mono-≤⁻ λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
        ≤⁻-mono (λ e → bind (F unit) (sort l₁) λ _ → e) $
        sort/is-bounded l₂
      )
    ⟩
      ( bind (F _) (choose (x ∷ xs)) λ (pivot , l , x∷xs↭pivot∷l) →
        bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
        bind (F _) (sort l₁) λ _ →
        step⋆ (length l₂ ²)
      )
    ≲⟨
      ( ≤⁻-mono
          {Π (Σ⁺ A λ pivot → Σ⁺ (list A) λ l' → meta⁺ (x ∷ xs ↭ pivot ∷ l')) λ _ → F unit}
          {F unit}
          (bind (F _) (choose (x ∷ xs)))
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
            bind (F _) (sort l₁) λ _ →
            step⋆ (length l₂ ²)}
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
            step⋆ (length l₁ ² + length l₂ ²)} $
        λ-mono-≤⁻ λ (pivot , l , x∷xs↭pivot∷l) →
        ≤⁻-mono
          {Π (Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ l)) λ _ → F unit}
          {F unit}
          (bind (F _) (partition pivot l)) $
        λ-mono-≤⁻ λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
        bind-irr-monoˡ-≤⁻ (sort/is-bounded l₁)
      )
    ⟩
      ( bind (F _) (choose (x ∷ xs)) λ (pivot , l , x∷xs↭pivot∷l) →
        bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
        step⋆ (length l₁ ² + length l₂ ²)
      )
    ≲⟨
      ( ≤⁻-mono
          {Π (Σ⁺ A λ pivot → Σ⁺ (list A) λ l' → meta⁺ (x ∷ xs ↭ pivot ∷ l')) λ _ → F unit}
          {F unit}
          (bind (F _) (choose (x ∷ xs)))
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
            step⋆ (length l₁ ² + length l₂ ²)}
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ _ →
            step⋆ (length l ²)} $
        λ-mono-≤⁻ λ (pivot , l , x∷xs↭pivot∷l) →
        ≤⁻-mono
          {Π (Σ⁺ (list A) λ l₁ → Σ⁺ (list A) λ l₂ → meta⁺ (All (_≤ pivot) l₁) ×⁺ meta⁺ (All (pivot ≤_) l₂) ×⁺ meta⁺ (l₁ ++ l₂ ↭ l)) λ _ → F unit}
          {F unit}
          (bind (F _) (partition pivot l)) $
        λ-mono-≤⁻ λ (l₁ , l₂ , h₁ , h₂ , l₁++l₂↭l) →
        ≤⁺-mono step⋆ $
        ≤⇒≤⁺ (Nat.≤-trans (sort/arithmetic (length l₁) (length l₂)) (Nat.≤-reflexive (Eq.cong _² (Eq.trans (Eq.sym (length-++ l₁)) (↭-length l₁++l₂↭l)))))
      )
    ⟩
      ( bind (F _) (choose (x ∷ xs)) λ (pivot , l , x∷xs↭pivot∷l) →
        bind (F _) (partition pivot l) λ _ →
        step⋆ (length l ²)
      )
    ≲⟨
      ( ≤⁻-mono
          {Π (Σ⁺ A λ pivot → Σ⁺ (list A) λ l' → meta⁺ (x ∷ xs ↭ pivot ∷ l')) λ _ → F unit}
          {F unit}
          (bind (F _) (choose (x ∷ xs)))
          {λ (pivot , l , x∷xs↭pivot∷l) →
            bind (F _) (partition pivot l) λ _ →
            step⋆ (length l ²)}
          {λ (pivot , l , x∷xs↭pivot∷l) →
            step⋆ (length l + length l ²)} $
        λ-mono-≤⁻ λ (pivot , l , x∷xs↭pivot∷l) →
        bind-irr-monoˡ-≤⁻ (partition/is-bounded pivot l)
      )
    ⟩
      ( bind (F _) (choose (x ∷ xs)) λ (pivot , l , x∷xs↭pivot∷l) →
        step⋆ (length l + length l ²)
      )
    ≡˘⟨
      ( Eq.cong (bind (F _) (choose (x ∷ xs))) $ funext λ (pivot , l , x∷xs↭pivot∷l) →
        Eq.cong (λ c → step⋆ (c + c ²)) {length xs} {length l} (Eq.cong Nat.pred (↭-length x∷xs↭pivot∷l))
      )
    ⟩
      ( bind (F _) (choose (x ∷ xs)) λ _ →
        step⋆ (length xs + length xs ²)
      )
    ≲⟨ bind-irr-monoˡ-≤⁻ (choose/is-bounded x xs) ⟩
      step⋆ (length xs + length xs ²)
    ≲⟨ step⋆-mono-≤⁻ (Nat.+-mono-≤ (Nat.n≤1+n (length xs)) (Nat.*-monoʳ-≤ (length xs) (Nat.n≤1+n (length xs)))) ⟩
      step⋆ (length (x ∷ xs) + length xs * length (x ∷ xs))
    ≡⟨⟩
      step⋆ (length (x ∷ xs) ²)
    ∎


module Lookup {A : tp⁺} where
  lookup : cmp $ Π (list A) λ _ → Π nat λ _ → F A
  lookup []       i       = fail (F _)
  lookup (x ∷ xs) zero    = ret x
  lookup (x ∷ xs) (suc i) = step (F _) 1 (lookup xs i)

  lookup/bound : cmp $ Π (list A) λ _ → Π nat λ _ → F A
  lookup/bound l i with i Nat.<? length l
  ... | yes p = step (F _) i (ret (List.lookup l (Fin.fromℕ< p)))
  ... | no _  = fail (F _)

  lookup/is-bounded : (l : val (list A)) (i : val nat) → lookup l i ≤⁻[ F A ] lookup/bound l i
  lookup/is-bounded l i with i Nat.<? length l
  ... | yes p = lemma l i p
    where
      lemma : (l : val (list A)) (i : val nat) (p : i Nat.< length l) → lookup l i ≤⁻[ F A ] step (F _) i (ret (List.lookup l (Fin.fromℕ< p)))
      lemma (x ∷ xs) zero (Nat.s≤s Nat.z≤n) = ≤⁻-refl
      lemma (x ∷ xs) (suc i) (Nat.s≤s p) = ≤⁻-mono (step (F _) 1) (lemma xs i p)
  ... | no ¬p = lemma l i (Nat.≮⇒≥ ¬p)
    where
      lemma : (l : val (list A)) (i : val nat) → i Nat.≥ length l → lookup l i ≤⁻[ F A ] fail (F A)
      lemma []       i       Nat.z≤n     = ≤⁻-refl
      lemma (x ∷ xs) (suc i) (Nat.s≤s p) =
        let open ≤⁻-Reasoning (F _) in
        begin
          step (F _) 1 (lookup xs i)
        ≲⟨ ≤⁻-mono (step (F _) 1) (lemma xs i p) ⟩
          step (F _) 1 (fail (F _))
        ≡⟨ fail/step 1 ⟩
          fail (F _)
        ∎


module Pervasive where
  e : cmp $ F bool
  e =
    branch (F bool)
      (step (F bool) 3 (ret true))
      (step (F bool) 12 (ret false))

  e/is-bounded : e ≤⁻[ F bool ] step (F bool) 12 (branch (F bool) (ret true) (ret false))
  e/is-bounded =
    let open ≤⁻-Reasoning (F bool) in
    begin
      e
    ≡⟨⟩
      branch (F bool)
        (step (F bool) 3 (ret true))
        (step (F bool) 12 (ret false))
    ≲⟨
      ≤⁻-mono
        (λ e → branch (F bool) e (step (F bool) 12 (ret false)))
        (step-monoˡ-≤⁻ {F bool} (ret true) (Nat.s≤s (Nat.s≤s (Nat.s≤s Nat.z≤n))))
    ⟩
      branch (F bool)
        (step (F bool) 12 (ret true))
        (step (F bool) 12 (ret false))
    ≡˘⟨ branch/step 12 ⟩
      step (F bool) 12 (branch (F bool) (ret true) (ret false))
    ∎

  e/is-bounded' : IsBounded bool e 12
  e/is-bounded' =
    let open ≤⁻-Reasoning (F unit) in
    begin
      bind (F unit) e (λ _ → ret triv)
    ≲⟨ ≤⁻-mono (λ e → bind (F _) e (λ _ → ret triv)) e/is-bounded ⟩
      bind (F unit) (step (F bool) 12 (branch (F bool) (ret true) (ret false))) (λ _ → ret triv)
    ≡⟨⟩
      step (F unit) 12 (branch (F unit) (ret triv) (ret triv))
    ≡⟨ Eq.cong (step (F unit) 12) branch/idem ⟩
      step⋆ 12
    ∎
