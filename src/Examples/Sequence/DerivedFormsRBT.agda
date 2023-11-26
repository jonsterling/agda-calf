{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.DerivedFormsRBT where

open import Algebra.Cost

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.Parallel parCostMonoid

open import Calf.Data.Nat
open import Calf.Data.List
open import Calf.Data.Product
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.IsBoundedG costMonoid
open import Data.List as List hiding (sum; map)
import Data.List.Properties as List
open import Data.Nat as Nat using (_+_; _*_)
import Data.Nat.Properties as Nat
open import Data.Nat.Logarithm

open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)

open import Examples.Sequence.RedBlackTree

module _ {A : Set} where
  list/preserves/length : ∀ (l₁ : List A) a (l₂ : List A) → 1 + (length l₁ + length l₂) ≡ length (l₁ ++ a ∷ l₂)
  list/preserves/length l₁ a l₂ =
    let open ≡-Reasoning in
    begin
      1 + (length l₁ + length l₂)
    ≡˘⟨ Nat.+-assoc 1 (length l₁) (length l₂) ⟩
      1 + length l₁ + length l₂
    ≡⟨ Eq.cong₂ _+_ (Nat.+-comm 1 (length l₁)) refl ⟩
      length l₁ + 1 + length l₂
    ≡⟨ Nat.+-assoc (length l₁) 1 (length l₂) ⟩
      length l₁ + (1 + length l₂)
    ≡⟨⟩
      length l₁ + length (a ∷ l₂)
    ≡˘⟨ List.length-++ l₁ ⟩
      length (l₁ ++ a ∷ l₂)
    ∎

  list/preserves/length' : ∀ (l₁ : List A) a (l₂ : List A) → (length l₁ + length l₂) + 1 ≡ length (l₁ ++ a ∷ l₂)
  list/preserves/length' l₁ a l₂ =
    let open ≡-Reasoning in
    begin
      (length l₁ + length l₂) + 1
    ≡⟨ Nat.+-comm (length l₁ + length l₂) 1 ⟩
      1 + (length l₁ + length l₂)
    ≡⟨ list/preserves/length l₁ a l₂ ⟩
      length (l₁ ++ a ∷ l₂)
    ∎


module MapReduce {A B : tp⁺} where
  mapreduce/seq : cmp $
    Π color λ y → Π nat λ n → Π (list A) λ l → Π (irbt A y n l) λ _ →
    Π (U (Π A λ _ → F B)) λ _ →
    Π (U (Π B λ _ → Π B λ _ → F B)) λ _ →
    Π B λ _ →
    F B
  mapreduce/seq .black .zero .[] leaf f g z = ret z
  mapreduce/seq .red n l (red t₁ a t₂) f g z =
    bind (F B)
      ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ s →
        bind (F B) (f a) (λ b →
          bind (F B) (g b (proj₂ s)) (λ s₃ →
            bind (F B) (g (proj₁ s) s₃) ret))
  mapreduce/seq .black n@(suc n') l (black t₁ a t₂) f g z =
    bind (F B)
      ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ s →
        bind (F B) (f a) (λ b →
          bind (F B) (g b (proj₂ s)) (λ s₃ →
            bind (F B) (g (proj₁ s) s₃) ret))

  mapreduce/work : val nat → val nat → val (list A) → val nat
  mapreduce/work c₁ c₂ l = (c₁ + 2 * c₂) * length l

  mapreduce/span : val nat → val nat → val color → val nat → val nat
  mapreduce/span c₁ c₂ red n = (2 * c₁ + 4 * c₂) * n + (c₁ + 2 * c₂)
  mapreduce/span c₁ c₂ black n = (2 * c₁ + 4 * c₂) * n

  mapreduce/span' : val nat → val nat → val nat → val nat
  mapreduce/span' c₁ c₂ n = (2 * c₁ + 4 * c₂) * n + (c₁ + 2 * c₂)

  span/bounded : (c₁ c₂ : val nat) → (y : val color) → (n : val nat) → mapreduce/span c₁ c₂ y n Nat.≤ mapreduce/span' c₁ c₂ n
  span/bounded c₁ c₂ red n = Nat.≤-refl
  span/bounded c₁ c₂ black n = Nat.m≤m+n ((2 * c₁ + 4 * c₂) * n) (c₁ + 2 * c₂)

  mapreduce/is-bounded' :
    {c₁ c₁' c₂ c₂' : val nat} →
    (f : cmp (Π A λ _ → F B)) →
    ({x : val A} → IsBounded B (f x) (c₁ , c₁')) →
    (g : cmp (Π B λ _ → Π B λ _ → F B)) →
    ({x y : val B} → IsBounded B (g x y) (c₂ , c₂')) →
    (z : val B) →
    (y : val color) → (n : val nat) → (l : val (list A)) → (t : val (irbt A y n l)) →
    IsBounded B (mapreduce/seq y n l t f g z) (mapreduce/work c₁ c₂ l , mapreduce/span c₁' c₂' y n)
  mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z .black .zero .[] leaf =
    Eq.subst₂
      (λ c c' → IsBounded B (mapreduce/seq black 0 [] leaf f g z) (c , c'))
      (Eq.sym (Nat.*-zeroʳ (c₁ + 2 * c₂)))
      (Eq.sym (Nat.*-zeroʳ (2 * c₁' + 4 * c₂')))
      ≤⁻-refl
  mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z .red n l (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (
          bind (F B)
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ _ →
              bind (F B) (f a) (λ _ →
                bind (F B) (g _ _) (λ _ →
                  bind (F B) (g _ _) ret)))
          (λ _ → ret triv)
      ≡⟨⟩
        (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ s₃ →
                  bind cost (g s₁ s₃) λ _ →
                    ret triv
        )
      ≤⟨ bind-monoʳ-≤⁻ ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) (λ (s₁ , s₂) →
           bind-monoʳ-≤⁻ (f a) (λ b →
             bind-monoʳ-≤⁻ (g b s₂) (λ s₃ → g-bound))) ⟩
       (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ _ →
                  step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoʳ-≤⁻ ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) (λ (s₁ , s₂) →
           bind-monoʳ-≤⁻ (f a) (λ b →
             bind-monoˡ-≤⁻ (λ _ → step⋆ (c₂ , c₂')) g-bound)) ⟩
        (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (step⋆ (c₂ , c₂')) λ _ →
                  step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoʳ-≤⁻ ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) (λ (s₁ , s₂) →
          bind-monoˡ-≤⁻ (λ _ → bind cost (step⋆ (c₂ , c₂')) λ _ → step⋆ (c₂ , c₂')) f-bound) ⟩
        (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (step⋆ (c₁ , c₁')) λ _ →
                bind cost (step⋆ (c₂ , c₂')) λ _ →
                  step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoˡ-≤⁻ (λ _ → bind cost (step⋆ (c₁ , c₁')) λ _ → bind cost (step⋆ (c₂ , c₂')) λ _ → step⋆ (c₂ , c₂'))
          (bound/par
            {e₁ = mapreduce/seq _ _ _ t₁ f g z}
            {c₁ = mapreduce/work c₁ c₂ l₁ , mapreduce/span c₁' c₂' black n}
            (mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z black n l₁ t₁)
            (mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z black n l₂ t₂)) ⟩
        (
          bind cost (step⋆ ((mapreduce/work c₁ c₂ l₁ , mapreduce/span c₁' c₂' black n) ⊗ (mapreduce/work c₁ c₂ l₂ , mapreduce/span c₁' c₂' black n))) λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂')
        )
      ≡⟨ Eq.cong
          (λ c → bind cost (step⋆ c) (λ _ →
                  bind cost (step⋆ (c₁ , c₁')) λ _ →
                    bind cost (step⋆ (c₂ , c₂')) λ _ →
                      step⋆ (c₂ , c₂')))
          {x = (mapreduce/work c₁ c₂ l₁ , mapreduce/span c₁' c₂' black n) ⊗ (mapreduce/work c₁ c₂ l₂ , mapreduce/span c₁' c₂' black n)}
          (Eq.cong₂ _,_ refl (Nat.⊔-idem (mapreduce/span c₁' c₂' black n))) ⟩
        (
          bind cost (step⋆ (((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂) , (2 * c₁' + 4 * c₂') * n)) λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂')
        )
      ≡⟨⟩
        step⋆ ((((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂)) + (c₁ + (c₂ + c₂)) ,
              ((2 * c₁' + 4 * c₂') * n) + (c₁' + (c₂' + c₂')))
      ≡⟨ Eq.cong₂ (λ c c' → step⋆ (c , c')) arithemtic₁ arithemtic₂ ⟩
        step⋆ (mapreduce/work c₁ c₂ l , mapreduce/span c₁' c₂' red n)
      ∎
        where
          arithemtic₁ : (((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂)) + (c₁ + (c₂ + c₂)) ≡ (c₁ + 2 * c₂) * length l
          arithemtic₁ =
            let open ≡-Reasoning in
            begin
              (((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂)) + (c₁ + (c₂ + c₂))
            ≡˘⟨ Eq.cong₂ _+_
                (Nat.*-distribˡ-+ (c₁ + 2 * c₂) (length l₁) (length l₂))
                (Eq.cong₂ _+_ {x = c₁} refl (Eq.trans (Nat.*-distribʳ-+ c₂ 1 1) (Eq.cong₂ _+_ (Nat.*-identityˡ c₂) (Nat.*-identityˡ c₂)))) ⟩
              ((c₁ + 2 * c₂) * (length l₁ + length l₂)) + (c₁ + 2 * c₂)
            ≡˘⟨ Eq.cong₂ _+_ refl (Nat.*-identityʳ (c₁ + 2 * c₂)) ⟩
              ((c₁ + 2 * c₂) * (length l₁ + length l₂)) + (c₁ + 2 * c₂) * 1
            ≡˘⟨ Nat.*-distribˡ-+ (c₁ + 2 * c₂) (length l₁ + length l₂) 1 ⟩
              (c₁ + 2 * c₂) * (length l₁ + length l₂ + 1)
            ≡⟨ Eq.cong₂ _*_ {x = c₁ + 2 * c₂} refl (list/preserves/length' l₁ a l₂) ⟩
              (c₁ + 2 * c₂) * length l
            ∎

          arithemtic₂ : (2 * c₁' + 4 * c₂') * n + (c₁' + (c₂' + c₂')) ≡ (2 * c₁' + 4 * c₂') * n + (c₁' + 2 * c₂')
          arithemtic₂ =
            let open ≡-Reasoning in
            begin
              (2 * c₁' + 4 * c₂') * n + (c₁' + (c₂' + c₂'))
            ≡˘⟨ Eq.cong₂ _+_
                {x = (2 * c₁' + 4 * c₂') * n}
                refl
                (Eq.cong₂ _+_ {x = c₁'} refl (Eq.trans (Nat.*-distribʳ-+ c₂' 1 1) (Eq.cong₂ _+_ (Nat.*-identityˡ c₂') (Nat.*-identityˡ c₂')))) ⟩
              (2 * c₁' + 4 * c₂') * n + (c₁' + 2 * c₂')
            ∎
  mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z .black n@(suc n') l (black {y₁ = y₁} {y₂ = y₂} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (
          bind (F B)
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ _ →
              bind (F B) (f a) (λ _ →
                bind (F B) (g _ _) (λ _ →
                  bind (F B) (g _ _) ret)))
          (λ _ → ret triv)
      ≡⟨⟩
        (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ s₃ →
                  bind cost (g s₁ s₃) λ _ →
                    ret triv
        )
      ≤⟨ bind-monoʳ-≤⁻ ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) (λ (s₁ , s₂) →
           bind-monoʳ-≤⁻ (f a) (λ b →
             bind-monoʳ-≤⁻ (g b s₂) (λ s₃ → g-bound))) ⟩
       (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (g b s₂) λ _ →
                  step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoʳ-≤⁻ ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) (λ (s₁ , s₂) →
           bind-monoʳ-≤⁻ (f a) (λ b →
             bind-monoˡ-≤⁻ (λ _ → step⋆ (c₂ , c₂')) g-bound)) ⟩
        (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (f a) λ b →
                bind cost (step⋆ (c₂ , c₂')) λ _ →
                  step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoʳ-≤⁻ ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) (λ (s₁ , s₂) →
          bind-monoˡ-≤⁻ (λ _ → bind cost (step⋆ (c₂ , c₂')) λ _ → step⋆ (c₂ , c₂')) f-bound) ⟩
        (
          bind cost
            ((mapreduce/seq _ _ _ t₁ f g z) ∥ (mapreduce/seq _ _ _ t₂ f g z)) λ (s₁ , s₂) →
              bind cost (step⋆ (c₁ , c₁')) λ _ →
                bind cost (step⋆ (c₂ , c₂')) λ _ →
                  step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoˡ-≤⁻ (λ _ → bind cost (step⋆ (c₁ , c₁')) λ _ → bind cost (step⋆ (c₂ , c₂')) λ _ → step⋆ (c₂ , c₂'))
          (bound/par
            {e₁ = mapreduce/seq _ _ _ t₁ f g z}
            {c₁ = mapreduce/work c₁ c₂ l₁ , mapreduce/span c₁' c₂' y₁ n'}
            (mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z y₁ n' l₁ t₁)
            (mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z y₂ n' l₂ t₂)) ⟩
        (
          bind cost (step⋆ ((mapreduce/work c₁ c₂ l₁ , mapreduce/span c₁' c₂' y₁ n') ⊗ (mapreduce/work c₁ c₂ l₂ , mapreduce/span c₁' c₂' y₂ n'))) λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂')
        )
      ≤⟨ bind-monoˡ-≤⁻
          (λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂'))
          (step⋆-mono-≤⁻ {c = mapreduce/work c₁ c₂ l₁ + mapreduce/work c₁ c₂ l₂ , mapreduce/span c₁' c₂' y₁ n' Nat.⊔ mapreduce/span c₁' c₂' y₂ n'}
            (Nat.≤-refl , Nat.⊔-mono-≤ (span/bounded c₁' c₂' y₁ n') (span/bounded c₁' c₂' y₂ n'))) ⟩
        (
          bind cost (step⋆ ((mapreduce/work c₁ c₂ l₁ , mapreduce/span' c₁' c₂' n') ⊗ (mapreduce/work c₁ c₂ l₂ , mapreduce/span' c₁' c₂' n'))) λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂')
        )
      ≡⟨ Eq.cong
          (λ c → bind cost (step⋆ c) λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂'))
          {x = mapreduce/work c₁ c₂ l₁ + mapreduce/work c₁ c₂ l₂ , mapreduce/span' c₁' c₂' n' Nat.⊔ mapreduce/span' c₁' c₂' n'}
          (Eq.cong₂ _,_ refl (Nat.⊔-idem ((2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂')))) ⟩
        (
          bind cost (step⋆ (((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂) , (2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂'))) λ _ →
            bind cost (step⋆ (c₁ , c₁')) λ _ →
              bind cost (step⋆ (c₂ , c₂')) λ _ →
                step⋆ (c₂ , c₂')
        )
      ≡⟨⟩
        step⋆ (((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂) + (c₁ + (c₂ + c₂)) ,
               ((2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂')) + (c₁' + (c₂' + c₂')) )
      ≡⟨ Eq.cong₂ (λ c c' → step⋆ (c , c')) arithemtic₁ arithemtic₂ ⟩
        step⋆ (mapreduce/work c₁ c₂ l , mapreduce/span c₁' c₂' black n)
      ∎
        where
          arithemtic₁ : ((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂) + (c₁ + (c₂ + c₂)) ≡ (c₁ + 2 * c₂) * length l
          arithemtic₁ =
            let open ≡-Reasoning in
            begin
              (((c₁ + 2 * c₂) * length l₁) + ((c₁ + 2 * c₂) * length l₂)) + (c₁ + (c₂ + c₂))
            ≡˘⟨ Eq.cong₂ _+_
                (Nat.*-distribˡ-+ (c₁ + 2 * c₂) (length l₁) (length l₂))
                (Eq.cong₂ _+_ {x = c₁} refl (Eq.trans (Nat.*-distribʳ-+ c₂ 1 1) (Eq.cong₂ _+_ (Nat.*-identityˡ c₂) (Nat.*-identityˡ c₂)))) ⟩
              ((c₁ + 2 * c₂) * (length l₁ + length l₂)) + (c₁ + 2 * c₂)
            ≡˘⟨ Eq.cong₂ _+_ refl (Nat.*-identityʳ (c₁ + 2 * c₂)) ⟩
              ((c₁ + 2 * c₂) * (length l₁ + length l₂)) + (c₁ + 2 * c₂) * 1
            ≡˘⟨ Nat.*-distribˡ-+ (c₁ + 2 * c₂) (length l₁ + length l₂) 1 ⟩
              (c₁ + 2 * c₂) * (length l₁ + length l₂ + 1)
            ≡⟨ Eq.cong₂ _*_ {x = c₁ + 2 * c₂} refl (list/preserves/length' l₁ a l₂) ⟩
              (c₁ + 2 * c₂) * length l
            ∎

          arithemtic₂ : ((2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂')) + (c₁' + (c₂' + c₂')) ≡ (2 * c₁' + 4 * c₂') * n
          arithemtic₂ =
            let open ≡-Reasoning in
            begin
              ((2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂')) + (c₁' + (c₂' + c₂'))
            ≡˘⟨ Eq.cong₂ _+_
                {x = (2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂')}
                refl
                (Eq.cong₂ _+_ {x = c₁'} refl (Eq.trans (Nat.*-distribʳ-+ c₂' 1 1) (Eq.cong₂ _+_ (Nat.*-identityˡ c₂') (Nat.*-identityˡ c₂')))) ⟩
              ((2 * c₁' + 4 * c₂') * n' + (c₁' + 2 * c₂')) + (c₁' + 2 * c₂')
            ≡⟨ Nat.+-assoc ((2 * c₁' + 4 * c₂') * n') (c₁' + 2 * c₂') (c₁' + 2 * c₂') ⟩
              (2 * c₁' + 4 * c₂') * n' + ((c₁' + 2 * c₂') + (c₁' + 2 * c₂'))
            ≡˘⟨ Eq.cong₂ _+_
                {x = (2 * c₁' + 4 * c₂') * n'}
                refl
                (Eq.trans (Nat.*-distribʳ-+ (c₁' + 2 * c₂') 1 1) (Eq.cong₂ _+_ (Nat.*-identityˡ (c₁' + 2 * c₂')) (Nat.*-identityˡ (c₁' + 2 * c₂')))) ⟩
              (2 * c₁' + 4 * c₂') * n' + 2 * (c₁' + 2 * c₂')
            ≡⟨ Eq.cong₂ _+_
                {x = (2 * c₁' + 4 * c₂') * n'}
                refl
                (Nat.*-distribˡ-+ 2 c₁' (2 * c₂')) ⟩
              (2 * c₁' + 4 * c₂') * n' + (2 * c₁' + 2 * (2 * c₂'))
            ≡⟨ Eq.cong (λ x → (2 * c₁' + 4 * c₂') * n' + (2 * c₁' + x)) (Eq.sym (Nat.*-assoc 2 2 c₂')) ⟩
              (2 * c₁' + 4 * c₂') * n' + (2 * c₁' + 4 * c₂')
            ≡⟨ Nat.+-comm ((2 * c₁' + 4 * c₂') * n') (2 * c₁' + 4 * c₂') ⟩
              (2 * c₁' + 4 * c₂') + (2 * c₁' + 4 * c₂') * n'
            ≡˘⟨ Nat.*-suc (2 * c₁' + 4 * c₂') n' ⟩
              (2 * c₁' + 4 * c₂') * n
            ∎

  mapreduce/is-bounded :
    {c₁ c₁' c₂ c₂' : val nat} →
    (f : cmp (Π A λ _ → F B)) →
    ({x : val A} → IsBounded B (f x) (c₁ , c₁')) →
    (g : cmp (Π B λ _ → Π B λ _ → F B)) →
    ({x y : val B} → IsBounded B (g x y) (c₂ , c₂')) →
    (z : val B) →
    (y : val color) → (n : val nat) → (l : val (list A)) → (t : val (irbt A y n l)) →
    IsBounded B (mapreduce/seq y n l t f g z) ((c₁ + 2 * c₂) * length l , (2 * c₁' + 4 * c₂') * ⌈log₂ (1 + length l) ⌉ + (c₁' + 2 * c₂'))
  mapreduce/is-bounded {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z y n l t =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (mapreduce/seq y n l t f g z) (λ _ → ret triv)
      ≤⟨ mapreduce/is-bounded' {c₁} {c₁'} {c₂} {c₂'} f f-bound g g-bound z y n l t ⟩
        step⋆ (mapreduce/work c₁ c₂ l , mapreduce/span c₁' c₂' y n)
      ≤⟨ step⋆-mono-≤⁻ (Nat.≤-refl {mapreduce/work c₁ c₂ l}, span/bounded c₁' c₂' y n) ⟩
        step⋆ (mapreduce/work c₁ c₂ l , mapreduce/span' c₁' c₂' n)
      ≤⟨ step⋆-mono-≤⁻ (Nat.≤-refl {mapreduce/work c₁ c₂ l} , lemma) ⟩
        step⋆ ((c₁ + 2 * c₂) * length l , (2 * c₁' + 4 * c₂') * ⌈log₂ (1 + length l) ⌉ + (c₁' + 2 * c₂'))
      ∎
        where
          lemma : mapreduce/span' c₁' c₂' n Nat.≤ (2 * c₁' + 4 * c₂') * ⌈log₂ (1 + length l) ⌉ + (c₁' + 2 * c₂')
          lemma =
            let open Nat.≤-Reasoning in
              begin
                (2 * c₁' + 4 * c₂') * n + (c₁' + 2 * c₂')
              ≤⟨ Nat.+-monoˡ-≤ (c₁' + 2 * c₂') (Nat.*-monoʳ-≤ (2 * c₁' + 4 * c₂') (i-nodes/bound/log-node-black-height t)) ⟩
                (2 * c₁' + 4 * c₂') * ⌈log₂ (1 + i-nodes t) ⌉ + (c₁' + 2 * c₂')
              ≡⟨ Eq.cong (λ x → (2 * c₁' + 4 * c₂') * ⌈log₂ (1 + x) ⌉ + (c₁' + 2 * c₂')) (i-nodes≡lengthl t) ⟩
                (2 * c₁' + 4 * c₂') * ⌈log₂ (1 + length l) ⌉ + (c₁' + 2 * c₂')
              ∎


module Sum where
  sum/seq : cmp $
    Π color λ y → Π nat λ n → Π (list nat) λ l → Π (irbt nat y n l) λ _ → F nat
  sum/seq .black .zero .[] leaf = ret 0
  sum/seq .red n l (red t₁ a t₂) =
    step (F nat) (1 , 1) $
      bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
      (λ (s₁ , s₂) → ret (s₁ + a + s₂))
  sum/seq .black n l (black t₁ a t₂) =
    step (F nat) (1 , 1) $
      bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
      (λ (s₁ , s₂) → ret (s₁ + a + s₂))

  span/sum : val color → val nat → val nat
  span/sum red n = 1 + 2 * n
  span/sum black n = 2 * n

  span/bounded : ∀ y n → (span/sum y n) Nat.≤ (1 + 2 * n)
  span/bounded red n = Nat.≤-refl
  span/bounded black n = Nat.n≤1+n (2 * n)

  sum/bounded' : ∀ y n l t → IsBounded nat (sum/seq y n l t) (length l , span/sum y n)
  sum/bounded' .black .zero .[] leaf = ≤⁻-refl
  sum/bounded' .red n l (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        step cost (1 , 1) (
          bind cost (
            bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
              (λ (s₁ , s₂) → ret (s₁ + a + s₂)))
          (λ _ → ret triv))
      ≡⟨⟩
        step cost (1 , 1) (
          bind cost ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
            (λ _ → ret triv))
      ≤⟨
        ≤⁻-mono
          (step cost (1 , 1))
          (bound/par
            {e₁ = sum/seq _ _ _ t₁}
            {c₁ = (length l₁ , span/sum black n)}
            (sum/bounded' black n l₁ t₁)
            (sum/bounded' black n l₂ t₂))
      ⟩
        step cost (1 , 1) (
          step⋆ ((length l₁ , span/sum black n) ⊗ (length l₂ , span/sum black n)))
      ≡⟨ Eq.cong (λ c → step cost (1 , 1) (step⋆ c)) (Eq.cong₂ _,_ refl (Nat.⊔-idem (span/sum black n))) ⟩
        step cost (1 , 1) (
          step⋆ (length l₁ + length l₂ , span/sum black n))
      ≡⟨⟩
        step⋆ (1 + (length l₁ + length l₂) , 1 + 2 * n)
      ≡⟨ Eq.cong₂ (λ c₁ c₂ → step⋆ (c₁ , c₂)) (list/preserves/length l₁ a l₂) refl ⟩
        step⋆ (length l , span/sum red n)
      ∎
  sum/bounded' .black n@(suc n') l (black {y₁ = y₁} {y₂ = y₂} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    let open ≤⁻-Reasoning cost in
      begin
        step cost (1 , 1) (
          bind cost (
            bind (F (nat)) ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
              (λ (s₁ , s₂) → ret (s₁ + a + s₂)))
          (λ _ → ret triv))
      ≡⟨⟩
        step cost (1 , 1) (
          bind cost ((sum/seq _ _ _ t₁) ∥ (sum/seq _ _ _ t₂))
            (λ _ → ret triv))
      ≤⟨ ≤⁻-mono
          (step cost (1 , 1))
          (bound/par
            {e₁ = sum/seq _ _ _ t₁}
            {c₁ = (length l₁ , span/sum y₁ n')}
            (sum/bounded' y₁ n' l₁ t₁)
            (sum/bounded' y₂ n' l₂ t₂)) ⟩
        step cost (1 , 1) (
          step⋆ ((length l₁ , span/sum y₁ n') ⊗ (length l₂ , span/sum y₂ n')))
      ≤⟨ ≤⁻-mono
          (λ e → step cost (1 , 1) e)
            (step⋆-mono-≤⁻
              (Nat.≤-refl , Nat.⊔-mono-≤ (span/bounded y₁ n') (span/bounded y₂ n'))) ⟩
        step cost (1 , 1) (
          step⋆ ((length l₁ , 1 + 2 * n') ⊗ (length l₂ , 1 + 2 * n')))
      ≡⟨ Eq.cong (λ c → step cost (1 , 1) (step⋆ c)) (Eq.cong₂ _,_ refl (Nat.⊔-idem (1 + 2 * n'))) ⟩
        step cost (1 , 1) (
          step⋆ (length l₁ + length l₂ , 1 + 2 * n'))
      ≡⟨⟩
        step⋆ (1 + (length l₁ + length l₂) , 1 + (1 + 2 * n'))
      ≡⟨ Eq.cong₂ (λ c₁ c₂ → step⋆ (c₁ , c₂)) (list/preserves/length l₁ a l₂) (arithemtic n') ⟩
       step⋆ (length l , span/sum black n)
      ∎
        where
          arithemtic : ∀ n → 1 + (1 + 2 * n) ≡ 2 * (suc n)
          arithemtic n =
            let open ≡-Reasoning in
            begin
              1 + (1 + 2 * n)
            ≡⟨ Nat.+-assoc 1 1 (2 * n) ⟩
              (1 + 1) + 2 * n
            ≡⟨⟩
              2 + 2 * n
            ≡˘⟨ Nat.*-suc 2 n ⟩
              2 * (suc n)
            ∎

  sum/bounded : ∀ y n l t → IsBounded nat (sum/seq y n l t) (length l , 1 + 2 * ⌈log₂ (1 + length l) ⌉)
  sum/bounded y n l t =
    let open ≤⁻-Reasoning cost in
      begin
        bind cost (sum/seq y n l t) (λ _ → ret triv)
      ≤⟨ sum/bounded' y n l t ⟩
        step⋆ (length l , span/sum y n)
      ≤⟨ step⋆-mono-≤⁻ (Nat.≤-refl {length l} , lemma) ⟩
        step⋆ (length l , 1 + 2 * ⌈log₂ (1 + length l) ⌉)
      ∎
    where
      lemma : span/sum y n Nat.≤ 1 + (2 * ⌈log₂ (1 + length l) ⌉)
      lemma =
        let open Nat.≤-Reasoning in
        begin
          span/sum y n
        ≤⟨ span/bounded y n ⟩
          1 + (2 * n)
        ≤⟨ Nat.s≤s (Nat.*-monoʳ-≤ 2 (i-nodes/bound/log-node-black-height t)) ⟩
          1 + (2 * ⌈log₂ (1 + i-nodes t) ⌉)
        ≡⟨ Eq.cong (λ x → 1 + (2 * ⌈log₂ (1 + x) ⌉)) (i-nodes≡lengthl t) ⟩
          1 + (2 * ⌈log₂ (1 + length l) ⌉)
        ∎
