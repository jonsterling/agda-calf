{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.RedBlackTree where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid

open import Calf.Data.Product
open import Calf.Data.Sum
open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid
open import Data.Nat as Nat using (_+_; _*_; _∸_)
open import Data.Nat.Logarithm
import Data.Nat.Properties as Nat
import Data.List.Properties as List

open import Function using (_$_)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)


data Color : Set where
  red : Color
  black : Color
color : tp⁺
color = meta⁺ Color

-- Indexed Red Black Tree
data IRBT (A : tp⁺) : val color → val nat → val (list A) → Set where
  leaf  : IRBT A black zero []
  red   : {n : val nat} {l₁ l₂ : val (list A)}
    (t₁ : IRBT A black n l₁) (a : val A) (t₂ : IRBT A black n l₂)
    → IRBT A red n (l₁ ++ [ a ] ++ l₂)
  black : {n : val nat} {y₁ y₂ : val color} {l₁ l₂ : val (list A)}
    (t₁ : IRBT A y₁ n l₁) (a : val A) (t₂ : IRBT A y₂ n l₂)
    → IRBT A black (suc n) (l₁ ++ [ a ] ++ l₂)
irbt : (A : tp⁺) → val color → val nat → val (list A) → tp⁺
irbt A y n l = meta⁺ (IRBT A y n l)


data AlmostLeftRBT (A : tp⁺) : (right-color : val color) → val nat → val (list A) → Set where
  violation :
    {n : val nat} {l₁ l₂ : val (list A)}
    → IRBT A red n l₁ → (a : val A) → IRBT A black n l₂
    → AlmostLeftRBT A red n (l₁ ++ [ a ] ++ l₂)
  valid :
    {right-color : val color} {n : val nat} {y : val color} {l : val (list A)} → IRBT A y n l
    → AlmostLeftRBT A right-color n l
alrbt : (A : tp⁺) → val color → val nat → val (list A) → tp⁺
alrbt A y n l = meta⁺ (AlmostLeftRBT A y n l)

joinLeftContCase₁ : ∀ l₁ l₂₁ l₂₂ a a₁ n₂ t₂₂ →
  (Σ (List (val A)) λ l → Σ ((l ≡ l₁ ++ [ a ] ++ l₂₁)) (λ _ → (AlmostLeftRBT A black n₂ l))) →
    cmp (F (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂₁ ++ [ a₁ ] ++ l₂₂)) ×⁺ (alrbt A red n₂ l)))
joinLeftContCase₁ {A} l₁ l₂₁ l₂₂ a a₁ n₂ t₂₂ (l , l≡l₂₁++a₁∷l₂₂ , valid {y = red} t') =
  ret (((l₁ ++ [ a ] ++ l₂₁) ++ [ a₁ ] ++ l₂₂) ,
    (List.++-assoc l₁ (a ∷ l₂₁) (a₁ ∷ l₂₂) ,
    (Eq.subst (λ l' → AlmostLeftRBT A red n₂ l') (Eq.cong₂ _++_ l≡l₂₁++a₁∷l₂₂ refl) (violation t' a₁ t₂₂))))
joinLeftContCase₁ {A} l₁ l₂₁ l₂₂ a a₁ n₂ t₂₂ (l , l≡l₂₁++a₁∷l₂₂ , valid {y = black} t') =
  ret (((l₁ ++ [ a ] ++ l₂₁) ++ [ a₁ ] ++ l₂₂) ,
    (List.++-assoc l₁ (a ∷ l₂₁) (a₁ ∷ l₂₂) ,
    Eq.subst (λ l' → AlmostLeftRBT A red n₂ l') (Eq.cong₂ _++_ l≡l₂₁++a₁∷l₂₂ refl) (valid (red t' a₁ t₂₂))))

joinLeftContCase₂ : ∀ l₁ l₂₁ l₂₂ a a₁ y₂₁ y₂₂ n₂ (t₂₂ : IRBT A y₂₂ n₂ l₂₂) →
  (Σ (List (val A))(λ a₂ → Σ (a₂ ≡ l₁ ++ a ∷ l₂₁) (λ x → AlmostLeftRBT A y₂₁ n₂ a₂))) →
    cmp (F (Σ⁺ (list A) (λ l → meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂) ×⁺ alrbt A black (suc n₂) l)))
joinLeftContCase₂ {A} l₁ l₂₁ l₂₂ a a₁ y₂₁ y₂₂ n₂ t₂₂ (l , l≡l₁++a∷l₂₁ , violation {l₂ = l'₂} (red {l₁ = l'₁₁} {l₂ = l'₁₂} t'₁₁ a'₁ t'₁₂) a' t'₂) =
  ret ((l'₁₁ ++ [ a'₁ ] ++ l'₁₂) ++ [ a' ] ++ (l'₂ ++ [ a₁ ] ++ l₂₂) ,
    ((begin
        (l'₁₁ ++ a'₁ ∷ l'₁₂) ++ a' ∷ l'₂ ++ a₁ ∷ l₂₂
      ≡˘⟨ List.++-assoc (l'₁₁ ++ a'₁ ∷ l'₁₂) (a' ∷ l'₂) (a₁ ∷ l₂₂) ⟩
        ((l'₁₁ ++ a'₁ ∷ l'₁₂) ++ a' ∷ l'₂) ++ a₁ ∷ l₂₂
      ≡⟨ Eq.cong₂ _++_ l≡l₁++a∷l₂₁ refl ⟩
        (l₁ ++ a ∷ l₂₁) ++ a₁ ∷ l₂₂
      ≡⟨ List.++-assoc l₁ (a ∷ l₂₁) (a₁ ∷ l₂₂) ⟩
        l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂
      ∎) ,
    (valid (red (black t'₁₁ a'₁ t'₁₂) a' (black t'₂ a₁ t₂₂)))))
      where open ≡-Reasoning
joinLeftContCase₂ {A} l₁ l₂₁ l₂₂ a a₁ y₂₁ y₂₂ n₂ t₂₂ (l , l≡l₁++a∷l₂₁ , valid t') =
  ret (((l₁ ++ [ a ] ++ l₂₁) ++ [ a₁ ] ++ l₂₂) ,
    (List.++-assoc l₁ (a ∷ l₂₁) (a₁ ∷ l₂₂) ,
    Eq.subst (λ l' → AlmostLeftRBT A black (suc n₂) l') (Eq.cong₂ _++_ l≡l₁++a∷l₂₁ refl) (valid (black t' a₁ t₂₂))))

joinLeft :
  cmp
    ( Π color λ y₁ → Π nat λ n₁ → Π (list A) λ l₁ → Π (irbt A y₁ n₁ l₁) λ _ →
      Π A λ a →
      Π color λ y₂ → Π nat λ n₂ → Π (list A) λ l₂ → Π (irbt A y₂ n₂ l₂) λ _ →
      Π (meta⁺ (n₁ < n₂)) λ _ →
      F (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (alrbt A y₂ n₂ l))
    )
joinLeft {A} y₁ n₁ l₁ t₁ a .red n₂ l₂ (red {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₁ t₂₂) n₁<n₂ =
  step (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂)) ×⁺ (alrbt A red n₂ l)))) (1 , 1) $
  bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂)) ×⁺ (alrbt A red n₂ l))))
    (joinLeft _ _ _ t₁ a _ _ _ t₂₁ n₁<n₂)
    (joinLeftContCase₁ l₁ l₂₁ l₂₂ a a₁ n₂ t₂₂)
joinLeft {A} y₁ n₁ l₁ t₁ a .black (suc n₂) l₂ (black {y₁ = y₂₁} {y₂ = y₂₂} {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₁ t₂₂) n₁<n₂ with n₁ Nat.≟ n₂
joinLeft {A} red n₁ l₁ (red {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a .black (suc n₁) l₂ (black {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₂ t₂₂) n₁<n₂ | yes refl =
  ret (((l₁₁ ++ [ a₁ ] ++ l₁₂) ++ [ a ] ++ (l₂₁ ++ [ a₂ ] ++ l₂₂)) ,
    (refl ,
    valid (red (black t₁₁ a₁ t₁₂) a (black t₂₁ a₂ t₂₂))))
joinLeft {A} black n₁ l₁ t₁ a .black (suc n₂) l₂ (black {y₁ = red} {l₂ = l₂₂} (red {l₁ = l₂₁₁} {l₂ = l₂₁₂} t₂₁₁ a₁₁ t₂₁₂) a₁ t₂₂) n₁<n₂ | yes refl =
  ret (((l₁ ++ [ a ] ++ l₂₁₁) ++ [ a₁₁ ] ++ (l₂₁₂ ++ [ a₁ ] ++ l₂₂)) ,
    ((begin
      (l₁ ++ [ a ] ++ l₂₁₁) ++ [ a₁₁ ] ++ l₂₁₂ ++ [ a₁ ] ++ l₂₂
    ≡⟨ List.++-assoc l₁ (a ∷ l₂₁₁) (a₁₁ ∷ l₂₁₂ ++ a₁ ∷ l₂₂) ⟩
      l₁ ++ a ∷ l₂₁₁ ++ a₁₁ ∷ l₂₁₂ ++ a₁ ∷ l₂₂
    ≡⟨ Eq.cong₂ _++_ refl (Eq.sym (List.++-assoc (a ∷ l₂₁₁) (a₁₁ ∷ l₂₁₂) (a₁ ∷ l₂₂))) ⟩
      l₁ ++ a ∷ (l₂₁₁ ++ [ a₁₁ ] ++ l₂₁₂) ++ a₁ ∷ l₂₂
    ∎) ,
    (valid (red (black t₁ a t₂₁₁) a₁₁ (black t₂₁₂ a₁ t₂₂)))))
      where open ≡-Reasoning
joinLeft {A} black n₁ l₁ t₁ a .black (suc n₂) l₂ (black {y₁ = black} {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₁ t₂₂) n₁<n₂ | yes refl =
  ret (((l₁ ++ [ a ] ++ l₂₁) ++ [ a₁ ] ++ l₂₂) ,
    ((List.++-assoc l₁ (a ∷ l₂₁) (a₁ ∷ l₂₂)) ,
    (valid (black (red t₁ a t₂₁) a₁ t₂₂))))
... | no n₁≢n₂ =
  step (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂)) ×⁺ (alrbt A black (suc n₂) l)))) (1 , 1) $
  bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂)) ×⁺ (alrbt A black (suc n₂) l))))
    (joinLeft _ _ _ t₁ a _ _ _ t₂₁ (Nat.≤∧≢⇒< (Nat.≤-pred n₁<n₂) n₁≢n₂))
    (joinLeftContCase₂ l₁ l₂₁ l₂₂ a a₁ y₂₁ y₂₂ n₂ t₂₂)

joinLeft/cost : (y : val color) (n₁ n₂ : val nat) → ℂ
joinLeft/cost red n₁ n₂ = (1 + (2 * (n₂ ∸ n₁)) , 1 + (2 * (n₂ ∸ n₁)))
joinLeft/cost black n₁ n₂ = ((2 * (n₂ ∸ n₁)) , (2 * (n₂ ∸ n₁)))

joinLeft/is-bounded' : ∀ y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁<n₂
  → IsBounded (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (alrbt A y₂ n₂ l)) (joinLeft y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁<n₂) (joinLeft/cost y₂ n₁ n₂)

joinLeft/is-bounded : ∀ {A} y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁<n₂
  → IsBounded (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (alrbt A y₂ n₂ l)) (joinLeft y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁<n₂) (1 + (2 * (n₂ ∸ n₁)) , 1 + (2 * (n₂ ∸ n₁)))

joinLeft/is-bounded' {A} y₁ n₁ l₁ t₁ a .red n₂ l₂ (red {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₁ t₂₂) n₁<n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      step cost (1 , 1) (
        bind cost (
          bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂)) ×⁺ (alrbt A red n₂ l))))
            (joinLeft _ _ _ t₁ a _ _ _ t₂₁ n₁<n₂)
            (joinLeftContCase₁ l₁ l₂₁ l₂₂ a a₁ n₂ t₂₂))
        (λ _ → ret triv))
    ≡⟨ Eq.cong
         (λ e → step cost (1 , 1) e)
         (Eq.cong
            (λ f → bind cost (joinLeft _ _ _ t₁ a _ _ _ t₂₁ n₁<n₂) f)
            (funext λ { (_ , _ , valid {y = red} _) → refl
                      ; (_ , _ , valid {y = black} _) → refl })) ⟩
      step cost (1 , 1) (
        bind cost (joinLeft _ _ _ t₁ a _ _ _ t₂₁ n₁<n₂)
        (λ _ → ret triv))
    ≤⟨ ≤⁻-mono (λ e → step cost (1 , 1) e) (joinLeft/is-bounded' _ _ _ t₁ a _ _ _ t₂₁ n₁<n₂) ⟩
      step cost (1 , 1) (
        bind cost (step⋆ (2 * (n₂ ∸ n₁) , 2 * (n₂ ∸ n₁))) λ _ → ret triv)
    ≤⟨ ≤⁻-refl ⟩
      step⋆ (1 + 2 * (n₂ ∸ n₁) , 1 + 2 * (n₂ ∸ n₁))
    ∎
joinLeft/is-bounded' {A} y₁ n₁ l₁ t₁ a .black (suc n₂) l₂ (black {y₁ = y₂₁} {y₂ = y₂₂} {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₁ t₂₂) n₁<n₂ with n₁ Nat.≟ n₂
joinLeft/is-bounded' red n₁ _ (red _ _ _) _ .black _ _ (black _ _ _) _ | yes refl =
  step⋆-mono-≤⁻ (Nat.z≤n {2 * (suc n₁ ∸ n₁)} , Nat.z≤n {2 * (suc n₁ ∸ n₁)})
joinLeft/is-bounded' black n₁ _ _ _ .black _ _ (black {y₁ = red} (red _ _ _) _ _) _ | yes refl =
  step⋆-mono-≤⁻ (Nat.z≤n {2 * (suc n₁ ∸ n₁)} , Nat.z≤n {2 * (suc n₁ ∸ n₁)})
joinLeft/is-bounded' black n₁ _ _ _ .black _ _ (black {y₁ = black} _ _ _) _ | yes refl =
  step⋆-mono-≤⁻ (Nat.z≤n {2 * (suc n₁ ∸ n₁)} , Nat.z≤n {2 * (suc n₁ ∸ n₁)})
...| no n₁≢n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      step cost (1 , 1) (
        bind cost (
          bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ l₁ ++ a ∷ l₂₁ ++ a₁ ∷ l₂₂)) ×⁺ (alrbt A black (suc n₂) l))))
            (joinLeft _ _ _ t₁ a _ _ _ t₂₁ (Nat.≤∧≢⇒< (Nat.≤-pred n₁<n₂) n₁≢n₂))
            (joinLeftContCase₂ l₁ l₂₁ l₂₂ a a₁ y₂₁ y₂₂ n₂ t₂₂))
        (λ _ → ret triv))
    ≡⟨ Eq.cong
         (λ e → step cost (1 , 1) e)
         (Eq.cong
           (λ f → bind cost (joinLeft _ _ _ t₁ a _ _ _ t₂₁ (Nat.≤∧≢⇒< (Nat.≤-pred n₁<n₂) n₁≢n₂)) f)
           (funext (λ { (_ , _ , violation (red _ _ _) _ _) → refl
                      ; (_ , _ , valid _) → refl }))) ⟩
      step cost (1 , 1) (
        bind cost (joinLeft _ _ _ t₁ a _ _ _ t₂₁ (Nat.≤∧≢⇒< (Nat.≤-pred n₁<n₂) n₁≢n₂))
        (λ _ → ret triv))
    ≤⟨ ≤⁻-mono (λ e → step cost (1 , 1) e) (joinLeft/is-bounded _ _ _ t₁ a _ _ _ t₂₁ _) ⟩
      step cost (1 , 1) (
        bind cost (step⋆ (1 + 2 * (n₂ ∸ n₁) , 1 + 2 * (n₂ ∸ n₁))) λ _ → ret triv)
    ≡⟨ Eq.cong (λ c → step⋆ c)
         (Eq.cong₂ _,_
           (Eq.trans (Eq.sym (Nat.*-suc 2 (n₂ ∸ n₁))) (Eq.cong (2 *_) (Eq.sym (Nat.+-∸-assoc 1 (Nat.≤-pred n₁<n₂)))))
           (Eq.trans (Eq.sym (Nat.*-suc 2 (n₂ ∸ n₁))) (Eq.cong (2 *_) (Eq.sym (Nat.+-∸-assoc 1 (Nat.≤-pred n₁<n₂)))))) ⟩
      step⋆ (2 * (suc n₂ ∸ n₁) , 2 * (suc n₂ ∸ n₁))
    ∎

joinLeft/is-bounded y₁ n₁ l₁ t₁ a red n₂ l₂ t₂ n₁<n₂ =
  joinLeft/is-bounded' y₁ n₁ l₁ t₁ a red n₂ l₂ t₂ n₁<n₂
joinLeft/is-bounded y₁ n₁ l₁ t₁ a black n₂ l₂ t₂ n₁<n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      bind cost (joinLeft y₁ n₁ l₁ t₁ a black n₂ l₂ t₂ n₁<n₂) (λ _ → ret triv)
    ≤⟨ joinLeft/is-bounded' y₁ n₁ l₁ t₁ a black n₂ l₂ t₂ n₁<n₂ ⟩
      step⋆ (2 * (n₂ ∸ n₁) , 2 * (n₂ ∸ n₁))
    ≤⟨ step⋆-mono-≤⁻ (Nat.n≤1+n _ , Nat.n≤1+n _) ⟩
      step⋆ (1 + 2 * (n₂ ∸ n₁) , 1 + 2 * (n₂ ∸ n₁))
    ∎

data AlmostRightRBT (A : tp⁺) : (left-color : val color) → val nat → val (list A) → Set where
  violation :
    {n : val nat} {l₁ l₂ : val (list A)}
    → IRBT A black n l₁ → (a : val A) → IRBT A red n l₂
    → AlmostRightRBT A red n (l₁ ++ [ a ] ++ l₂)
  valid :
    {left-color : val color} {n : val nat} {y : val color} {l : val (list A)} → IRBT A y n l
    → AlmostRightRBT A left-color n l
arrbt : (A : tp⁺) → val color → val nat → val (list A) → tp⁺
arrbt A y n l = meta⁺ (AlmostRightRBT A y n l)

joinRightContCase₁ : ∀ l₁₁ l₁₂ l₂ a a₁ n₁ t₁₁ →
  (Σ (List (val A)) (λ a₂ → Σ (a₂ ≡ l₁₂ ++ a ∷ l₂) (λ x → AlmostRightRBT A black n₁ a₂))) →
    cmp (F (Σ⁺ (list A) (λ l → meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂) ×⁺ arrbt A red n₁ l)))
joinRightContCase₁ {A} l₁₁ l₁₂ l₂ a a₁ n₁ t₁₁ (l , l≡l₁₂++a₁∷l₂ , valid {y = red} t') =
  ret (l₁₁ ++ [ a₁ ] ++ (l₁₂ ++ [ a ] ++ l₂) ,
    Eq.sym (List.++-assoc l₁₁ (a₁ ∷ l₁₂) (a ∷ l₂)) ,
    Eq.subst (λ l' → AlmostRightRBT A red n₁ l') (Eq.cong₂ _++_ refl (Eq.cong₂ _∷_ refl l≡l₁₂++a₁∷l₂)) (violation t₁₁ a₁ t'))
joinRightContCase₁ {A} l₁₁ l₁₂ l₂ a a₁ n₁ t₁₁ (l , l≡l₁₂++a₁∷l₂ , valid {y = black} t') =
  ret (l₁₁ ++ [ a₁ ] ++ (l₁₂ ++ [ a ] ++ l₂) ,
    Eq.sym (List.++-assoc l₁₁ (a₁ ∷ l₁₂) (a ∷ l₂)) ,
    Eq.subst (λ l' → AlmostRightRBT A red n₁ l') (Eq.cong₂ _++_ refl (Eq.cong₂ _∷_ refl l≡l₁₂++a₁∷l₂)) (valid (red t₁₁ a₁ t')))

joinRightContCase₂ : ∀ l₁₁ l₁₂ l₂ a a₁ y₁₁ y₁₂ n₁ (t₁₁ : IRBT A y₁₁ n₁ l₁₁) →
  (Σ (List (val A)) (λ a₂ → Σ (a₂ ≡ l₁₂ ++ a ∷ l₂) (λ x → AlmostRightRBT A y₁₂ n₁ a₂))) →
    cmp (F (Σ⁺ (list A) (λ l → meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂) ×⁺ arrbt A black (suc n₁) l)))
joinRightContCase₂ {A} l₁₁ l₁₂ l₂ a a₁ y₁₁ y₁₂ n₁ t₁₁ (l , l≡l₁₂++a∷l₂ , violation {l₁ = l'₁} t'₁ a' (red {l₁ = l'₂₁} {l₂ = l'₂₂} t'₂₁ a'₂ t'₂₂)) =
  ret ((l₁₁ ++ [ a₁ ] ++ l'₁) ++ [ a' ] ++ (l'₂₁ ++ [ a'₂ ] ++ l'₂₂) ,
    (begin
      (l₁₁ ++ a₁ ∷ l'₁) ++ a' ∷ l'₂₁ ++ a'₂ ∷ l'₂₂
    ≡⟨ List.++-assoc l₁₁ (a₁ ∷ l'₁) (a' ∷ l'₂₁ ++ a'₂ ∷ l'₂₂) ⟩
      l₁₁ ++ a₁ ∷ l'₁ ++ a' ∷ l'₂₁ ++ a'₂ ∷ l'₂₂
    ≡⟨ Eq.cong₂ _++_ refl (Eq.cong₂ _∷_ refl l≡l₁₂++a∷l₂) ⟩
      l₁₁ ++ a₁ ∷ l₁₂ ++ a ∷ l₂
    ≡˘⟨ List.++-assoc l₁₁ (a₁ ∷ l₁₂) (a ∷ l₂) ⟩
      (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂
    ∎) ,
    (valid (red (black t₁₁ a₁ t'₁) a' (black t'₂₁ a'₂ t'₂₂))))
      where open ≡-Reasoning
joinRightContCase₂ {A} l₁₁ l₁₂ l₂ a a₁ y₁₁ y₁₂ n₁ t₁₁(l , l≡l₁₂++a∷l₂ , valid t') =
  ret (l₁₁ ++ [ a₁ ] ++ (l₁₂ ++ [ a ] ++ l₂) ,
    Eq.sym (List.++-assoc l₁₁ (a₁ ∷ l₁₂) (a ∷ l₂)) ,
    Eq.subst (λ l' → AlmostRightRBT A black (suc n₁) l') (Eq.cong₂ _++_ refl (Eq.cong₂ _∷_ refl l≡l₁₂++a∷l₂)) (valid (black t₁₁ a₁ t')))

joinRight :
  cmp
    ( Π color λ y₁ → Π nat λ n₁ → Π (list A) λ l₁ → Π (irbt A y₁ n₁ l₁) λ _ →
      Π A λ a →
      Π color λ y₂ → Π nat λ n₂ → Π (list A) λ l₂ → Π (irbt A y₂ n₂ l₂) λ _ →
      Π (meta⁺ (n₁ > n₂)) λ _ →
      F (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (arrbt A y₁ n₁ l))
    )
joinRight {A} .red n₁ l₁ (red {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a y₂ n₂ l₂ t₂ n₁>n₂ =
  step (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂)) ×⁺ (arrbt A red n₁ l)))) (1 , 1) $
  bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂)) ×⁺ (arrbt A red n₁ l))))
    (joinRight _ _ _ t₁₂ a _ _ _ t₂ n₁>n₂)
    (joinRightContCase₁ l₁₁ l₁₂ l₂ a a₁ n₁ t₁₁)
joinRight {A} .black (suc n₁) l₁ (black {y₁ = y₁₁} {y₂ = y₁₂} {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a y₂ n₂ l₂ t₂ n₁>n₂ with n₁ Nat.≟ n₂
joinRight {A} .black (suc n₁) l₁ (black {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a red n₁ l₂ (red {l₁ = l₂₁} {l₂ = l₂₂} t₂₁ a₂ t₂₂) n₁>n₂ | yes refl =
  ret ((l₁₁ ++ [ a₁ ] ++ l₁₂) ++ [ a ] ++ (l₂₁ ++ [ a₂ ] ++ l₂₂) ,
    refl ,
    valid (red (black t₁₁ a₁ t₁₂) a (black t₂₁ a₂ t₂₂)))
joinRight {A} .black (suc n₁) l₁ (black {y₂ = red} {l₁ = l₁₁} t₁₁ a₁ (red {l₁ = l₁₂₁} {l₂ = l₁₂₂} t₁₂₁ a₁₂ t₁₂₂)) a black n₁ l₂ t₂ n₁>n₂ | yes refl =
  ret ((l₁₁ ++ [ a₁ ] ++ l₁₂₁) ++ [ a₁₂ ] ++ (l₁₂₂ ++ [ a ] ++ l₂) ,
    (begin
      (l₁₁ ++ a₁ ∷ l₁₂₁) ++ a₁₂ ∷ l₁₂₂ ++ a ∷ l₂
    ≡⟨ List.++-assoc l₁₁ (a₁ ∷ l₁₂₁) (a₁₂ ∷ l₁₂₂ ++ a ∷ l₂) ⟩
      l₁₁ ++ a₁ ∷ l₁₂₁ ++ a₁₂ ∷ l₁₂₂ ++ a ∷ l₂
    ≡⟨ Eq.cong₂ _++_ refl (Eq.sym (List.++-assoc (a₁ ∷ l₁₂₁) (a₁₂ ∷ l₁₂₂) (a ∷ l₂))) ⟩
      l₁₁ ++ (a₁ ∷ l₁₂₁ ++ a₁₂ ∷ l₁₂₂) ++ a ∷ l₂
    ≡˘⟨ List.++-assoc l₁₁ (a₁ ∷ l₁₂₁ ++ a₁₂ ∷ l₁₂₂) (a ∷ l₂) ⟩
      (l₁₁ ++ a₁ ∷ l₁₂₁ ++ a₁₂ ∷ l₁₂₂) ++ a ∷ l₂
    ∎) ,
    valid (red (black t₁₁ a₁ t₁₂₁) a₁₂ (black t₁₂₂ a t₂)))
      where open ≡-Reasoning
joinRight {A} .black (suc n₁) l₁ (black {y₂ = black} {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a black n₁ l₂ t₂ n₁>n₂ | yes refl =
  ret (l₁₁ ++ [ a₁ ] ++ (l₁₂ ++ [ a ] ++ l₂) ,
    Eq.sym (List.++-assoc l₁₁ (a₁ ∷ l₁₂) (a ∷ l₂)) ,
    valid (black t₁₁ a₁ (red t₁₂ a t₂)))
... | no n₁≢n₂ =
  step (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂)) ×⁺ (arrbt A black (suc n₁) l)))) (1 , 1) $
  bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂)) ×⁺ (arrbt A black (suc n₁) l))))
    (joinRight _ _ _ t₁₂ a _ _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred n₁>n₂) (≢-sym n₁≢n₂)))
    (joinRightContCase₂ l₁₁ l₁₂ l₂ a a₁ y₁₁ y₁₂ n₁ t₁₁)

joinRight/cost : (y : val color) (n₁ n₂ : val nat) → ℂ
joinRight/cost red n₁ n₂ = 1 + (2 * (n₁ ∸ n₂)) , 1 + (2 * (n₁ ∸ n₂))
joinRight/cost black n₁ n₂ = (2 * (n₁ ∸ n₂)) , (2 * (n₁ ∸ n₂))

joinRight/is-bounded' : ∀ y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂
  → IsBounded (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (arrbt A y₁ n₁ l)) (joinRight y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂) (joinRight/cost y₁ n₁ n₂)

joinRight/is-bounded : ∀ {A} y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂
  → IsBounded (Σ⁺ (list A) λ l → (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ (arrbt A y₁ n₁ l)) (joinRight y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂) (1 + (2 * (n₁ ∸ n₂)) , 1 + (2 * (n₁ ∸ n₂)))

joinRight/is-bounded' {A} red n₁ l₁ (red {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a y₂ n₂ l₂ t₂ n₁>n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      step cost (1 , 1) (
        bind cost (
          bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂)) ×⁺ (arrbt A red n₁ l))))
            (joinRight _ _ _ t₁₂ a _ _ _ t₂ n₁>n₂)
            (joinRightContCase₁ l₁₁ l₁₂ l₂ a a₁ n₁ t₁₁))
        (λ _ → ret triv))
    ≡⟨ Eq.cong
         (λ e → step cost (1 , 1) e)
         (Eq.cong
           (λ f → bind cost (joinRight _ _ _ t₁₂ a _ _ _ t₂ n₁>n₂) f)
           (funext ((λ { (_ , _ , valid {y = red} _) → refl
                       ; (_ , _ , valid {y = black} _) → refl })))) ⟩
      step cost (1 , 1) (
        bind cost (joinRight _ _ _ t₁₂ a _ _ _ t₂ n₁>n₂)
        (λ _ → ret triv))
    ≤⟨ ≤⁻-mono (λ e → step cost (1 , 1) e) (joinRight/is-bounded' _ _ _ t₁₂ a _ _ _ t₂ n₁>n₂) ⟩
      step cost (1 , 1) (
        bind cost (step⋆ (2 * (n₁ ∸ n₂) , 2 * (n₁ ∸ n₂))) λ _ → ret triv)
    ≤⟨ ≤⁻-refl ⟩
      step⋆ (1 + 2 * (n₁ ∸ n₂) , 1 + 2 * (n₁ ∸ n₂))
    ∎
joinRight/is-bounded' {A} black (suc n₁) l₁ (black {y₁ = y₁₁} {y₂ = y₁₂} {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a₁ t₁₂) a y₂ n₂ l₂ t₂ n₁>n₂ with n₁ Nat.≟ n₂
joinRight/is-bounded' black n₁ _ (black _ _ _) _ red _ _ (red _ _ _) _ | yes refl =
  step⋆-mono-≤⁻ (Nat.z≤n {2 * (suc n₁ ∸ n₁)} , Nat.z≤n {2 * (suc n₁ ∸ n₁)})
joinRight/is-bounded' black n₁ _ (black {y₂ = red} _ _ (red _ _ _)) _ black _ _ _ _ | yes refl =
  step⋆-mono-≤⁻ (Nat.z≤n {2 * (suc n₁ ∸ n₁)} , Nat.z≤n {2 * (suc n₁ ∸ n₁)})
joinRight/is-bounded' black n₁ _ (black {y₂ = black} _ _ _) _ black _ _ _ _ | yes refl =
  step⋆-mono-≤⁻ (Nat.z≤n {2 * (suc n₁ ∸ n₁)} , Nat.z≤n {2 * (suc n₁ ∸ n₁)})
... | no n₁≢n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      step cost (1 , 1) (
        bind cost (
          bind (F (Σ⁺ (list A) (λ l → (meta⁺ (l ≡ (l₁₁ ++ a₁ ∷ l₁₂) ++ a ∷ l₂)) ×⁺ (arrbt A black (suc n₁) l))))
            (joinRight _ _ _ t₁₂ a _ _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred n₁>n₂) (≢-sym n₁≢n₂)))
            (joinRightContCase₂ l₁₁ l₁₂ l₂ a a₁ y₁₁ y₁₂ n₁ t₁₁))
        (λ _ → ret triv))
    ≡⟨ Eq.cong
        (λ e → step cost (1 , 1) e)
          (Eq.cong
            (λ f → bind cost (joinRight _ _ _ t₁₂ a _ _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred n₁>n₂) (≢-sym n₁≢n₂))) f)
            (funext (λ { (_ , _ , violation _ _ (red _ _ _)) → refl
                       ; (_ , _ , valid _) → refl }))) ⟩
      step cost (1 , 1) (
        bind cost (joinRight _ _ _ t₁₂ a _ _ _ t₂ (Nat.≤∧≢⇒< (Nat.≤-pred n₁>n₂) (≢-sym n₁≢n₂)))
        (λ _ → ret triv))
    ≤⟨ ≤⁻-mono (λ e → step cost (1 , 1) e) (joinRight/is-bounded _ _ _ t₁₂ a _ _ _ t₂ _) ⟩
      step cost (1 , 1) (
        bind cost (step⋆ (1 + 2 * (n₁ ∸ n₂) , 1 + 2 * (n₁ ∸ n₂))) λ _ → ret triv)
    ≡⟨ Eq.cong (λ c → step⋆ c)
         (Eq.cong₂ _,_
           (Eq.trans (Eq.sym (Nat.*-suc 2 (n₁ ∸ n₂))) (Eq.cong (2 *_) (Eq.sym (Nat.+-∸-assoc 1 n₁>n₂))))
           (Eq.trans (Eq.sym (Nat.*-suc 2 (n₁ ∸ n₂))) (Eq.cong (2 *_) (Eq.sym (Nat.+-∸-assoc 1 n₁>n₂))))) ⟩
      step⋆ (2 * (suc n₁ ∸ n₂) , 2 * (suc n₁ ∸ n₂))
    ∎

joinRight/is-bounded red n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂ =
  joinRight/is-bounded' red n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂
joinRight/is-bounded black n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      bind cost (joinRight black n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂) (λ _ → ret triv)
    ≤⟨ joinRight/is-bounded' black n₁ l₁ t₁ a y₂ n₂ l₂ t₂ n₁>n₂ ⟩
      step⋆ (2 * (n₁ ∸ n₂) , 2 * (n₁ ∸ n₂))
    ≤⟨ step⋆-mono-≤⁻ (Nat.n≤1+n _ , Nat.n≤1+n _) ⟩
      step⋆ (1 + 2 * (n₁ ∸ n₂) , 1 + 2 * (n₁ ∸ n₂))
    ∎

i-joinContCaseLeft : ∀ l₁ l₂ a y₂ n₁ n₂ n₁<n₂ →
  (Σ (List (val A)) (λ a₁ → Σ (a₁ ≡ l₁ ++ a ∷ l₂) (λ x → AlmostLeftRBT A y₂ n₂ a₁))) →
    cmp (F (Σ⁺ color (λ y → Σ⁺ (list A) (λ l → meta⁺ (l ≡ l₁ ++ a ∷ l₂) ×⁺ (irbt A y (suc (n₁ ⊔ n₂)) l ⊎⁺ irbt A y (n₁ ⊔ n₂) l)))))
i-joinContCaseLeft {A} l₁ l₂ a y₂ n₁ n₂ n₁<n₂ (l , l≡l₁++a∷l₂ , violation {l₁ = l'₁} {l₂ = l'₂} t'₁ a' t'₂) =
  ret (black , l'₁ ++ [ a' ] ++ l'₂ , l≡l₁++a∷l₂ ,
    inj₁ (Eq.subst (λ n → IRBT A black (suc n) (l'₁ ++ a' ∷ l'₂)) (Eq.sym (Nat.m≤n⇒m⊔n≡n (Nat.<⇒≤ n₁<n₂)))
    (black t'₁ a' t'₂)))
i-joinContCaseLeft {A} l₁ l₂ a y₂ n₁ n₂ n₁<n₂ (l , l≡l₁++a∷l₂ , valid {n = n} {y = y} {l = l} t') =
  ret (y , l , l≡l₁++a∷l₂ , inj₂ (Eq.subst (λ n → IRBT A y n l) (Eq.sym (Nat.m≤n⇒m⊔n≡n (Nat.<⇒≤ n₁<n₂))) t'))

i-joinContCaseRight : ∀ l₁ l₂ a y₁ n₁ n₂ n₁>n₂ →
  (Σ (List (val A)) (λ a₁ → Σ (a₁ ≡ l₁ ++ a ∷ l₂) (λ x → AlmostRightRBT A y₁ n₁ a₁))) →
    cmp (F (Σ⁺ color (λ y → Σ⁺ (list A) (λ l → meta⁺ (l ≡ l₁ ++ a ∷ l₂) ×⁺ (irbt A y (suc (n₁ ⊔ n₂)) l ⊎⁺ irbt A y (n₁ ⊔ n₂) l)))))
i-joinContCaseRight {A} l₁ l₂ a y₁ n₁ n₂ n₁>n₂ (l , l≡l₁++a∷l₂ , violation {l₁ = l'₁} {l₂ = l'₂} t'₁ a' t'₂) =
  ret (black , l'₁ ++ [ a' ] ++ l'₂ , l≡l₁++a∷l₂ ,
    inj₁ (Eq.subst (λ n → IRBT A black (suc n) (l'₁ ++ a' ∷ l'₂)) (Eq.sym (Nat.m≥n⇒m⊔n≡m (Nat.<⇒≤ n₁>n₂)))
    (black t'₁ a' t'₂)))
i-joinContCaseRight {A} l₁ l₂ a y₁ n₁ n₂ n₁>n₂ (l , l≡l₁++a∷l₂ , valid {n = n} {y = y} {l = l} t') =
  ret (y , l , l≡l₁++a∷l₂ , inj₂ (Eq.subst (λ n → IRBT A y n l) (Eq.sym (Nat.m≥n⇒m⊔n≡m (Nat.<⇒≤ n₁>n₂))) t'))

i-join :
  cmp
    ( Π color λ y₁ → Π nat λ n₁ → Π (list A) λ l₁ → Π (irbt A y₁ n₁ l₁) λ _ →
      Π A λ a →
      Π color λ y₂ → Π nat λ n₂ → Π (list A) λ l₂ → Π (irbt A y₂ n₂ l₂) λ _ →
      F (Σ⁺ color λ y → Σ⁺ (list A) λ l →
        (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ ((irbt A y (1 + (n₁ Nat.⊔ n₂)) l) ⊎⁺ (irbt A y (n₁ Nat.⊔ n₂) l)))
    )
i-join {A} y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ with Nat.<-cmp n₁ n₂
i-join {A} red n₁ l₁ t₁ a y₂ n₂ l₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
  ret (black , l₁ ++ [ a ] ++ l₂ , refl ,
    inj₁ (Eq.subst (λ n → IRBT A black (suc n) (l₁ ++ a ∷ l₂)) (Eq.sym (Nat.⊔-idem n₁)) (black t₁ a t₂)))
i-join {A} black n₁ l₁ t₁ a red n₂ l₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
  ret (black , l₁ ++ [ a ] ++ l₂ , refl ,
    inj₁ (Eq.subst (λ n → IRBT A black (suc n) (l₁ ++ a ∷ l₂)) (Eq.sym (Nat.⊔-idem n₁)) (black t₁ a t₂)))
i-join {A} black n₁ l₁ t₁ a black n₂ l₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
  ret (red , l₁ ++ [ a ] ++ l₂ , refl ,
    inj₂ (Eq.subst (λ n → IRBT A red n (l₁ ++ a ∷ l₂)) (Eq.sym (Nat.⊔-idem n₁)) (red t₁ a t₂)))
... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ =
  bind (F (Σ⁺ color λ y → Σ⁺ (list A) λ l →
        (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ ((irbt A y (1 + (n₁ Nat.⊔ n₂)) l) ⊎⁺ (irbt A y (n₁ Nat.⊔ n₂) l))))
    (joinLeft _ _ _ t₁ a _ _ _ t₂ n₁<n₂)
    (i-joinContCaseLeft l₁ l₂ a y₂ n₁ n₂ n₁<n₂)
... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
  bind (F (Σ⁺ color λ y → Σ⁺ (list A) λ l →
        (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ ((irbt A y (1 + (n₁ Nat.⊔ n₂)) l) ⊎⁺ (irbt A y (n₁ Nat.⊔ n₂) l))))
    (joinRight _ _ _ t₁ a _ _ _ t₂ n₁>n₂)
    (i-joinContCaseRight l₁ l₂ a y₁ n₁ n₂ n₁>n₂)

i-join/is-bounded : ∀ {A} y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂
  → IsBounded (Σ⁺ color λ y → Σ⁺ (list A) λ l →
        (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ ((irbt A y (1 + (n₁ Nat.⊔ n₂)) l) ⊎⁺ (irbt A y (n₁ Nat.⊔ n₂) l))) (i-join y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂)
          (1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)) , 1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)))
i-join/is-bounded {A} y₁ n₁ l₁ t₁ a y₂ n₂ l₂ t₂ with Nat.<-cmp n₁ n₂
i-join/is-bounded {A} red n₁ l₁ t₁ a y₂ .n₁ l₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
  step⋆-mono-≤⁻ (Nat.z≤n {1 + (2 * (n₁ Nat.⊔ n₁ ∸ n₁ Nat.⊓ n₁))}, Nat.z≤n {1 + (2 * (n₁ Nat.⊔ n₁ ∸ n₁ Nat.⊓ n₁))})
i-join/is-bounded {A} black n₁ l₁ t₁ a red n₁ l₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
  step⋆-mono-≤⁻ (Nat.z≤n {1 + (2 * (n₁ Nat.⊔ n₁ ∸ n₁ Nat.⊓ n₁))}, Nat.z≤n {1 + (2 * (n₁ Nat.⊔ n₁ ∸ n₁ Nat.⊓ n₁))})
i-join/is-bounded {A} black n₁ l₁ t₁ a black n₁ l₂ t₂ | tri≈ ¬n₁<n₂ refl ¬n₁>n₂ =
  step⋆-mono-≤⁻ (Nat.z≤n {1 + (2 * (n₁ Nat.⊔ n₁ ∸ n₁ Nat.⊓ n₁))}, Nat.z≤n {1 + (2 * (n₁ Nat.⊔ n₁ ∸ n₁ Nat.⊓ n₁))})
... | tri< n₁<n₂ n₁≢n₂ ¬n₁>n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      bind cost (
        bind (F (Σ⁺ color λ y → Σ⁺ (list A) λ l →
          (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ ((irbt A y (1 + (n₁ Nat.⊔ n₂)) l) ⊎⁺ (irbt A y (n₁ Nat.⊔ n₂) l))))
            (joinLeft _ _ _ t₁ a _ _ _ t₂ n₁<n₂)
            (i-joinContCaseLeft l₁ l₂ a y₂ n₁ n₂ n₁<n₂))
      (λ _ → ret triv)
    ≡⟨ Eq.cong
         (λ f → bind cost (joinLeft _ _ _ t₁ a _ _ _ t₂ n₁<n₂) f)
         (funext (λ { (_ , _ , violation _ _ _) → refl
                    ; (_ , _ , valid _) → refl })) ⟩
      bind cost (joinLeft _ _ _ t₁ a _ _ _ t₂ n₁<n₂) (λ _ → ret triv)
    ≤⟨ joinLeft/is-bounded _ _ _ t₁ a _ _ _ t₂ n₁<n₂ ⟩
      step⋆ (1 + 2 * (n₂ ∸ n₁) , 1 + 2 * (n₂ ∸ n₁))
    ≡⟨ Eq.cong (λ c → step⋆ c)
         (Eq.cong₂ _,_
           (Eq.cong (1 +_) (Eq.cong (2 *_) (Eq.cong₂ _∸_ (Eq.sym (Nat.m≤n⇒m⊔n≡n (Nat.<⇒≤ n₁<n₂))) (Eq.sym (Nat.m≤n⇒m⊓n≡m (Nat.<⇒≤ n₁<n₂))))))
           (Eq.cong (1 +_) (Eq.cong (2 *_) (Eq.cong₂ _∸_ (Eq.sym (Nat.m≤n⇒m⊔n≡n (Nat.<⇒≤ n₁<n₂))) (Eq.sym (Nat.m≤n⇒m⊓n≡m (Nat.<⇒≤ n₁<n₂))))))) ⟩
      step⋆ (1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)) , 1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)))
    ∎
... | tri> ¬n₁<n₂ n₁≢n₂ n₁>n₂ =
  let open ≤⁻-Reasoning cost in
    begin
      bind cost (
        bind (F (Σ⁺ color λ y → Σ⁺ (list A) λ l →
          (meta⁺ (l ≡ l₁ ++ [ a ] ++ l₂)) ×⁺ ((irbt A y (1 + (n₁ Nat.⊔ n₂)) l) ⊎⁺ (irbt A y (n₁ Nat.⊔ n₂) l))))
            (joinRight _ _ _ t₁ a _ _ _ t₂ n₁>n₂)
            (i-joinContCaseRight l₁ l₂ a y₁ n₁ n₂ n₁>n₂))
      (λ _ → ret triv)
    ≡⟨ Eq.cong
         (λ f → bind cost (joinRight _ _ _ t₁ a _ _ _ t₂ n₁>n₂) f)
           (funext (λ { (_ , _ , violation _ _ _) → refl
                      ; (_ , _ , valid _) → refl })) ⟩
      bind cost (joinRight _ _ _ t₁ a _ _ _ t₂ n₁>n₂) (λ _ → ret triv)
    ≤⟨ joinRight/is-bounded _ _ _ t₁ a _ _ _ t₂ n₁>n₂ ⟩
      step⋆ (1 + 2 * (n₁ ∸ n₂) , 1 + 2 * (n₁ ∸ n₂))
    ≡⟨ Eq.cong (λ c → step⋆ c)
         (Eq.cong₂ _,_
           (Eq.cong (1 +_) (Eq.cong (2 *_) (Eq.cong₂ _∸_ (Eq.sym (Nat.m≥n⇒m⊔n≡m (Nat.<⇒≤ n₁>n₂))) (Eq.sym (Nat.m≥n⇒m⊓n≡n (Nat.<⇒≤ n₁>n₂))))))
           (Eq.cong (1 +_) (Eq.cong (2 *_) (Eq.cong₂ _∸_ (Eq.sym (Nat.m≥n⇒m⊔n≡m (Nat.<⇒≤ n₁>n₂))) (Eq.sym (Nat.m≥n⇒m⊓n≡n (Nat.<⇒≤ n₁>n₂))))))) ⟩
      step⋆ (1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)) , 1 + (2 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)))
    ∎

i-nodes : {y : val color} {n : val nat} {l : val (list A)} → IRBT A y n l → val nat
i-nodes leaf = 0
i-nodes (red t₁ _ t₂) = 1 + (i-nodes t₁) + (i-nodes t₂)
i-nodes (black t₁ _ t₂) = 1 + (i-nodes t₁) + (i-nodes t₂)

i-nodes≡lengthl : ∀ {y} {n} {l} → (t : IRBT A y n l) → i-nodes t ≡ length l
i-nodes≡lengthl leaf = refl
i-nodes≡lengthl (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
  begin
    1 + (i-nodes t₁) + (i-nodes t₂)
  ≡⟨ Eq.cong₂ _+_ (Eq.cong₂ _+_ refl (i-nodes≡lengthl t₁)) (i-nodes≡lengthl t₂) ⟩
    1 + length l₁ + length l₂
  ≡⟨ Eq.cong₂ _+_ (Nat.+-comm 1 (length l₁)) refl ⟩
    (length l₁ + 1) + length l₂
  ≡⟨ Nat.+-assoc (length l₁) 1 (length l₂) ⟩
    length l₁ + (1 + length l₂)
  ≡⟨⟩
    length l₁ + length ([ a ] ++ l₂)
  ≡˘⟨ List.length-++ l₁ ⟩
    length (l₁ ++ [ a ] ++ l₂)
  ∎
    where open ≡-Reasoning
i-nodes≡lengthl (black {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
  begin
    1 + (i-nodes t₁) + (i-nodes t₂)
  ≡⟨ Eq.cong₂ _+_ (Eq.cong₂ _+_ refl (i-nodes≡lengthl t₁)) (i-nodes≡lengthl t₂) ⟩
    1 + length l₁ + length l₂
  ≡⟨ Eq.cong₂ _+_ (Nat.+-comm 1 (length l₁)) refl ⟩
    (length l₁ + 1) + length l₂
  ≡⟨ Nat.+-assoc (length l₁) 1 (length l₂) ⟩
    length l₁ + (1 + length l₂)
  ≡⟨⟩
    length l₁ + length ([ a ] ++ l₂)
  ≡˘⟨ List.length-++ l₁ ⟩
    length (l₁ ++ [ a ] ++ l₂)
  ∎
    where open ≡-Reasoning

i-total-height : {y : val color} {n : val nat} {l : val (list A)} → IRBT A y n l → val nat
i-total-height leaf = 0
i-total-height (red t₁ _ t₂) = 1 + (i-total-height t₁ Nat.⊔ i-total-height t₂)
i-total-height (black t₁ _ t₂) = 1 + (i-total-height t₁ Nat.⊔ i-total-height t₂)

i-nodes/bound/node-black-height : {y : val color} {n : val nat} {l : val (list A)} → (t : IRBT A y n l) → 1 + (i-nodes t) Nat.≥ (2 Nat.^ n)
i-nodes/bound/node-black-height leaf = Nat.s≤s Nat.z≤n
i-nodes/bound/node-black-height (red {n} t₁ _ t₂) =
  let open Nat.≤-Reasoning in
    begin
      2 Nat.^ n
    ≤⟨ i-nodes/bound/node-black-height t₁ ⟩
      suc (i-nodes t₁)
    ≤⟨ Nat.m≤m+n (suc (i-nodes t₁)) (suc (i-nodes t₂)) ⟩
      (suc (i-nodes t₁)) + (suc (i-nodes t₂))
    ≡⟨ Eq.cong suc (Nat.+-suc (i-nodes t₁) (i-nodes t₂)) ⟩
      suc (suc (i-nodes t₁ + i-nodes t₂))
    ∎
i-nodes/bound/node-black-height (black {n} t₁ _ t₂) =
  let open Nat.≤-Reasoning in
    begin
      (2 Nat.^ n) + ((2 Nat.^ n) + zero)
    ≡⟨ Eq.sym (Eq.trans (Eq.sym (Nat.+-identityʳ ((2 Nat.^ n) + (2 Nat.^ n)))) (Nat.+-assoc ((2 Nat.^ n)) ((2 Nat.^ n)) 0)) ⟩
      (2 Nat.^ n) + (2 Nat.^ n)
    ≤⟨ Nat.+-monoʳ-≤ (2 Nat.^ n) (i-nodes/bound/node-black-height t₂) ⟩
      (2 Nat.^ n) + (suc (i-nodes t₂))
    ≤⟨ Nat.+-monoˡ-≤ ((suc (i-nodes t₂))) (i-nodes/bound/node-black-height t₁) ⟩
      (suc (i-nodes t₁)) + (suc (i-nodes t₂))
    ≡⟨ Eq.cong suc (Nat.+-suc (i-nodes t₁) (i-nodes t₂)) ⟩
      suc (suc (i-nodes t₁ + i-nodes t₂))
    ∎

i-nodes/bound/log-node-black-height : {y : val color} {n : val nat} {l : val (list A)} → (t : IRBT A y n l) → n Nat.≤ ⌈log₂ (1 + (i-nodes t)) ⌉
i-nodes/bound/log-node-black-height {A} {y} {n} t =
  let open Nat.≤-Reasoning in
    begin
      n
    ≡⟨ Eq.sym (⌈log₂2^n⌉≡n n) ⟩
      ⌈log₂ (2 Nat.^ n) ⌉
    ≤⟨ ⌈log₂⌉-mono-≤ (i-nodes/bound/node-black-height t) ⟩
      ⌈log₂ (1 + (i-nodes t)) ⌉
    ∎

total-height/black-height : {y : val color} {n : val nat} {l : val (list A)} → (t : IRBT A y n l) → (i-total-height t) Nat.≤ (2 * n + 1)
total-height/black-height leaf = Nat.z≤n
total-height/black-height (red leaf _ leaf) = Nat.s≤s Nat.z≤n
total-height/black-height (red (black {n} t₁₁ _ t₁₂) _ (black t₂₁ _ t₂₂)) =
  let open Nat.≤-Reasoning in
    begin
      suc (suc ((i-total-height t₁₁ Nat.⊔ i-total-height t₁₂) Nat.⊔ (i-total-height t₂₁ Nat.⊔ i-total-height t₂₂)))
    ≤⟨ Nat.s≤s (Nat.s≤s (Nat.⊔-mono-≤ (Nat.⊔-mono-≤ (total-height/black-height t₁₁) (total-height/black-height t₁₂)) (Nat.⊔-mono-≤ (total-height/black-height t₂₁) (total-height/black-height t₂₂)))) ⟩
      suc (suc (((2 * n + 1) Nat.⊔ (2 * n + 1)) Nat.⊔ ((2 * n + 1) Nat.⊔ (2 * n + 1))))
    ≡⟨ Eq.cong suc (Eq.cong suc (Nat.m≤n⇒m⊔n≡n Nat.≤-refl)) ⟩
      suc (suc ((2 * n + 1) Nat.⊔ (2 * n + 1)))
    ≡⟨ Eq.cong suc (Eq.cong suc (Nat.m≤n⇒m⊔n≡n Nat.≤-refl)) ⟩
      suc (suc (2 * n + 1))
    ≡⟨ Eq.cong suc (Eq.trans (Eq.cong suc (Nat.+-assoc n (n + zero) 1)) (Eq.sym (Nat.+-suc n ((n + zero) + 1)))) ⟩
      suc (n + suc ((n + zero) + 1))
    ≡⟨ Eq.cong suc (Eq.sym (Nat.+-assoc n (suc (n + zero)) 1)) ⟩
      2 * (suc n) + 1
    ∎
total-height/black-height (black {n} t₁ _ t₂) =
  let open Nat.≤-Reasoning in
    begin
      suc (i-total-height t₁ Nat.⊔ i-total-height t₂)
    ≤⟨ Nat.s≤s (Nat.⊔-mono-≤ (total-height/black-height t₁) (total-height/black-height t₂)) ⟩
      suc ((2 * n + 1) Nat.⊔ (2 * n + 1))
    ≡⟨ Eq.cong suc (Nat.m≤n⇒m⊔n≡n Nat.≤-refl) ⟩
      suc (2 * n + 1)
    ≤⟨ Nat.s≤s (Nat.+-monoˡ-≤ 1 (Nat.+-monoʳ-≤ n (Nat.n≤1+n (n + zero)))) ⟩
      2 * (suc n) + 1
    ∎

i-nodes/bound/total-height : {y : val color} {n : val nat} {l : val (list A)} → (t : IRBT A y n l) → (1 + (i-nodes t)) Nat.≤ (2 Nat.^ (i-total-height t))
i-nodes/bound/total-height leaf = Nat.s≤s Nat.z≤n
i-nodes/bound/total-height (red t₁ _ t₂) =
  let open Nat.≤-Reasoning in
    begin
      suc (suc (i-nodes t₁ + i-nodes t₂))
    ≡⟨ Eq.cong suc (Eq.sym (Nat.+-suc (i-nodes t₁) (i-nodes t₂))) ⟩
      (suc (i-nodes t₁) + (suc (i-nodes t₂)))
    ≤⟨ Nat.+-monoˡ-≤ (suc (i-nodes t₂)) (i-nodes/bound/total-height t₁) ⟩
      (2 Nat.^ (i-total-height t₁)) + (suc (i-nodes t₂))
    ≤⟨ Nat.+-monoʳ-≤ (2 Nat.^ (i-total-height t₁)) (i-nodes/bound/total-height t₂) ⟩
      (2 Nat.^ (i-total-height t₁)) + (2 Nat.^ (i-total-height t₂))
    ≤⟨ Nat.+-monoˡ-≤ ((2 Nat.^ (i-total-height t₂))) (Nat.^-monoʳ-≤ 2 {x = i-total-height t₁} (Nat.m≤n⇒m≤n⊔o (i-total-height t₂) (Nat.≤-refl))) ⟩
      (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + (2 Nat.^ (i-total-height t₂))
    ≤⟨ Nat.+-monoʳ-≤ ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))) ((Nat.^-monoʳ-≤ 2 {x = i-total-height t₂} (Nat.m≤n⇒m≤o⊔n (i-total-height t₁) (Nat.≤-refl)))) ⟩
      (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))
    ≡⟨ Eq.trans (Eq.sym (Nat.+-identityʳ ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))))) (Nat.+-assoc ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))) ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))) 0) ⟩
      ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + zero))
    ∎
i-nodes/bound/total-height (black t₁ _ t₂) =
  let open Nat.≤-Reasoning in
    begin
      suc (suc (i-nodes t₁ + i-nodes t₂))
    ≡⟨ Eq.cong suc (Eq.sym (Nat.+-suc (i-nodes t₁) (i-nodes t₂))) ⟩
      (suc (i-nodes t₁) + (suc (i-nodes t₂)))
    ≤⟨ Nat.+-monoˡ-≤ (suc (i-nodes t₂)) (i-nodes/bound/total-height t₁) ⟩
      (2 Nat.^ (i-total-height t₁)) + (suc (i-nodes t₂))
    ≤⟨ Nat.+-monoʳ-≤ (2 Nat.^ (i-total-height t₁)) (i-nodes/bound/total-height t₂) ⟩
      (2 Nat.^ (i-total-height t₁)) + (2 Nat.^ (i-total-height t₂))
    ≤⟨ Nat.+-monoˡ-≤ ((2 Nat.^ (i-total-height t₂))) (Nat.^-monoʳ-≤ 2 {x = i-total-height t₁} (Nat.m≤n⇒m≤n⊔o (i-total-height t₂) (Nat.≤-refl))) ⟩
      (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + (2 Nat.^ (i-total-height t₂))
    ≤⟨ Nat.+-monoʳ-≤ ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))) ((Nat.^-monoʳ-≤ 2 {x = i-total-height t₂} (Nat.m≤n⇒m≤o⊔n (i-total-height t₁) (Nat.≤-refl)))) ⟩
      (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))
    ≡⟨ Eq.trans (Eq.sym (Nat.+-identityʳ ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + (2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))))) (Nat.+-assoc ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))) ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂))) 0) ⟩
      ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + ((2 Nat.^ (i-total-height t₁ Nat.⊔ i-total-height t₂)) + zero))
    ∎

i-nodes/lower-bound/node-black-height : {y : val color} {n : val nat} {l : val (list A)}  → (t : IRBT A y n l) → (1 + (i-nodes t)) Nat.≤ (2 Nat.^ (2 * n + 1))
i-nodes/lower-bound/node-black-height {A} {y} {n} t =
  let open Nat.≤-Reasoning in
    begin
      1 + (i-nodes t)
    ≤⟨ i-nodes/bound/total-height t ⟩
      2 Nat.^ (i-total-height t)
    ≤⟨ Nat.^-monoʳ-≤ 2 (total-height/black-height t) ⟩
      2 Nat.^ (2 * n + 1)
    ∎

i-nodes/lower-bound/log-node-black-height : {y : val color} {n : val nat} {l : val (list A)} → (t : IRBT A y n l) → n Nat.≥ ⌊ (⌈log₂ (1 + (i-nodes t)) ⌉ ∸ 1) /2⌋
i-nodes/lower-bound/log-node-black-height {A} {y} {n} t =
  let open Nat.≤-Reasoning in
    begin
      ⌊ (⌈log₂ (1 + (i-nodes t)) ⌉ ∸ 1) /2⌋
    ≤⟨ Nat.⌊n/2⌋-mono (h t) ⟩
      ⌊ (2 * n) /2⌋
    ≡⟨ Eq.sym (Eq.trans (Nat.n≡⌊n+n/2⌋ n) (Eq.cong ⌊_/2⌋ (Eq.cong₂ _+_ refl (Eq.sym (Nat.+-identityʳ n))))) ⟩
      n
    ∎
    where
      m≤o+n⇒m∸n≤o : (m n o : val nat) → (m Nat.≤ (o + n)) → ((m ∸ n) Nat.≤ o)
      m≤o+n⇒m∸n≤o m n o m≤o+n =
        let open Nat.≤-Reasoning in
          begin
            m ∸ n
          ≤⟨ Nat.∸-monoˡ-≤ n m≤o+n ⟩
            (o + n) ∸ n
          ≡⟨ Nat.m+n∸n≡m o n ⟩
            o
          ∎

      h : {y : val color} {n : val nat} {l : val (list A)} → (t : IRBT A y n l) → (⌈log₂ (1 + (i-nodes t)) ⌉ ∸ 1) Nat.≤ (2 * n)
      h {y} {n} t = m≤o+n⇒m∸n≤o ⌈log₂ (1 + (i-nodes t)) ⌉ 1 (2 * n) (
        let open Nat.≤-Reasoning in
          begin
            ⌈log₂ (1 + (i-nodes t)) ⌉
          ≤⟨ ⌈log₂⌉-mono-≤ (i-nodes/lower-bound/node-black-height t) ⟩
            ⌈log₂ (2 Nat.^ (2 * n + 1)) ⌉
          ≡⟨ ⌈log₂2^n⌉≡n (2 * n + 1) ⟩
            2 * n + 1
          ∎)


i-rec : {A : tp⁺} {X : tp⁻} →
  cmp
    ( Π (U X) λ _ →
      Π
        ( U
          ( Π color λ y₁ → Π nat λ n₁ → Π (list A) λ l₁ → Π (irbt A y₁ n₁ l₁) λ _ → Π (U X) λ _ →
            Π A λ _ →
            Π color λ y₂ → Π nat λ n₂ → Π (list A) λ l₂ → Π (irbt A y₂ n₂ l₂) λ _ → Π (U X) λ _ →
            X
          )
        ) λ _ →
      Π color λ y → Π nat λ n → Π (list A) λ l → Π (irbt A y n l) λ _ →
      X
    )
i-rec {A} {X} z f .black .zero .[] leaf = z
i-rec {A} {X} z f .red n .(_ ++ [ a ] ++ _) (red t₁ a t₂) =
  f
    _ _ _ t₁ (i-rec {A} {X} z f _ _ _ t₁)
    a
    _ _ _ t₂ (i-rec {A} {X} z f _ _ _ t₂)
i-rec {A} {X} z f .black .(suc _) .(_ ++ [ a ] ++ _) (black t₁ a t₂) =
  f
    _ _ _ t₁ (i-rec {A} {X} z f _ _ _ t₁)
    a
    _ _ _ t₂ (i-rec {A} {X} z f _ _ _ t₂)
