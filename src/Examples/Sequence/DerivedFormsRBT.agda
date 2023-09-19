{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.DerivedFormsRBT where

open import Examples.Sequence.RedBlackTree

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid

open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Bounded costMonoid
open import Data.Product
import Data.Nat.Properties as Nat
import Data.List.Properties as List
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_; _∸_)
open import Data.List as List

open import Level using (0ℓ)
open import Function using (_$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)

variable
  y₁ y₂ : val color
  n₁ n₂ : val nat

record RBT (A : tp pos) (l : val (list A)) : Set where
  constructor ⟪_⟫
  field
    {y} : val color
    {n} : val nat
    t : val (irbt A y n l)
rbt : (A : tp pos) → val (list A) → tp pos
rbt A l = U (meta (RBT A l))

mk : {l l' : val (list A)} → val (rbt A l) → l ≡ l' → val (rbt A l')
mk t h = Eq.subst (λ l → RBT _ l) h t

bound : val color → val nat → val nat → val nat
bound red n₁ n₂ = 2 + (n₁ Nat.⊔ n₂)
bound black n₁ n₂ = 1 + (n₁ Nat.⊔ n₂)

summ :
  cmp (
    Π color λ y₁ → Π nat λ n₁ → Π (list nat) λ l₁ → Π (irbt nat y₁ n₁ l₁) λ _ → F nat
  )
summ .black .zero .[] leaf = ret 0
summ .red n .(_ ++ [ a ] ++ _) (red t₁ a t₂) =
  step (F nat) (1 , 1) $
    bind (F (nat)) ((summ _ _ _ t₁) & (summ _ _ _ t₂))
    (λ (s₁ , s₂) → ret (s₁ + a + s₂))
summ .black .(suc _) .(_ ++ [ a ] ++ _) (black t₁ a t₂) =
  step (F nat) (1 , 1) $
    bind (F (nat)) ((summ _ _ _ t₁) & (summ _ _ _ t₂))
    (λ (s₁ , s₂) → ret (s₁ + a + s₂))

span/sum : val color → val nat → val nat
span/sum red n = 1 + 2 * n
span/sum black n = 2 * n

span/bounded : ∀ y n → (span/sum y n) Nat.≤ (1 + 2 * n)
span/bounded red n = Nat.≤-refl
span/bounded black n = Nat.n≤1+n (2 * n)

summ/bounded : ∀ y n l t → IsBounded nat (summ y n l t) (List.length l , span/sum y n)
summ/bounded .black .zero .[] leaf = bound/relax (λ x → Nat.z≤n , Nat.z≤n) bound/ret
summ/bounded .red n l (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
  Eq.subst
    (IsBounded _ _) {y = List.length l , 1 + 2 * n}
    {!   !}
    (bound/step (1 , 1) (List.length l₁ + List.length l₂  , 2 * n)
      (Eq.subst
        (IsBounded _ _) {x = List.length l₁ + List.length l₂ + 0 , 2 * n + 0}
        {!   !}
        (bound/bind/const
          (List.length l₁ + List.length l₂  , 2 * n)
          𝟘
          (Eq.subst
            (IsBounded _ _)
            {!   !}
            (bound/par (summ/bounded _ _ _ t₁) (summ/bounded _ _ _ t₂)))
          (λ _ → bound/ret)))
    )
summ/bounded .black n@(suc n') l (black {y₁ = y₁} {y₂ = y₂} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
  Eq.subst
    (IsBounded _ _) {y = List.length l , 2 * (suc n') }
    {!   !}
    (bound/step (1 , 1) (List.length l₁ + List.length l₂ ,  1 + 2 * n')
      (Eq.subst
        (IsBounded _ _)  {x = List.length l₁ + List.length l₂ + 0 , 1 + 2 * n' + 0}
        {!   !}
        (bound/bind/const (List.length l₁ + List.length l₂ , 1 + 2 * n') 𝟘
          (Eq.subst
            (IsBounded _ _)
            {!   !}
            (bound/par
              (bound/relax (λ u → Nat.≤-refl , (span/bounded y₁ n')) (summ/bounded _ _ _ t₁))
              (bound/relax (λ u → Nat.≤-refl , (span/bounded y₂ n')) (summ/bounded _ _ _ t₂))))
          (λ a₁ → bound/ret))))

-- summ : cmp (Π (seq nat) λ _ → F (nat))
--   summ =
--     rec
--       {X = F (nat)}
--       (ret 0)
--       λ t'₁ ih₁ a' t'₂ ih₂ →
--         step (F nat) (1 , 1) $
--         bind (F (nat)) (ih₁ & ih₂)
--         (λ (s₁ , s₂) → ret (s₁ + a' + s₂))

-- i-rec {A} {X} z f .black .zero .[] leaf = z
-- i-rec {A} {X} z f .red n .(_ ++ [ a ] ++ _) (red t₁ a t₂) =
--   f
--     _ _ _ t₁ (i-rec {A} {X} z f _ _ _ t₁)
--     a
--     _ _ _ t₂ (i-rec {A} {X} z f _ _ _ t₂)
-- i-rec {A} {X} z f .black .(suc _) .(_ ++ [ a ] ++ _) (black t₁ a t₂) =
--   f
--     _ _ _ t₁ (i-rec {A} {X} z f _ _ _ t₁)
--     a
--     _ _ _ t₂ (i-rec {A} {X} z f _ _ _ t₂)


-- append :
--   cmp (
--     Π color λ y₁ → Π nat λ n₁ → Π (list A) λ l₁ → Π (irbt A y₁ n₁ l₁) λ _ →
--     Π color λ y₂ → Π nat λ n₂ → Π (list A) λ l₂ → Π (irbt A y₂ n₂ l₂) λ _ →
--     F (Σ++ color λ y → Σ++ nat λ n → prod⁺ (U (meta (n ≤ (bound y₁ n₁ n₂)))) (irbt A y n (l₁ ++ l₂)))
--   )
-- append {A} y₁ n₁ .[] leaf y₂ n₂ l₂             t₂ =
--   ret (y₂ , n₂ , Nat.n≤1+n n₂ , t₂)
-- append {A} y₁ n₁ l₁ (red   t₁₁ a t₁₂) y₂ n₂ l₂ t₂ =
--   bind (F (Σ++ color λ y → Σ++ nat λ n → prod⁺ (U (meta (n ≤ (bound y₁ n₁ n₂)))) (irbt A y n (l₁ ++ l₂))))
--     (append _ _ _ t₁₂ _ _ _ t₂)
--     λ { (y , n , p , t₂') →
--       bind (F (Σ++ color λ y → Σ++ nat λ n → prod⁺ (U (meta (n ≤ (bound y₁ n₁ n₂)))) (irbt A y n (l₁ ++ l₂))))
--       (i-join _ _ _ t₁₁ a _ _ _ t₂')
--       (λ { (y₂' , l , l≡l₁₁++a++l₂' , inj₁ t₂) → ret (y₂' , 1 + (n₁ Nat.⊔ n) , {!   !} , {! t₂  !})
--          ; (y₂' , l , l≡l₁₁++a++l₂' , inj₂ t₂) → ret (y₂' , n₁ Nat.⊔ n , {!   !} , {!   !})
--       })
--     }
--   -- step (F (rbt A (l₁ ++ l₂))) 1 $
--   -- bind (F (rbt A (l₁ ++ l₂))) (append _ _ _ t₁₂ _ _ _ t₂) λ { ⟪ t₂' ⟫ →
--   -- bind (F (rbt A (l₁ ++ l₂)))  (i-join _ _ _ t₁₁ a _ _ _ t₂')
--   --   λ { (_ , l , l≡l₁₁++a++l₂' , inj₁ t₂) →
--   --       ret (mk ⟪ t₂ ⟫ (Eq.trans l≡l₁₁++a++l₂' (Eq.sym (List.++-assoc _ ([ a ] ++ _) l₂))))
--   --     ; (_ , l , l≡l₁₁++a++l₂' , inj₂ t₂) →
--   --       ret (mk ⟪ t₂ ⟫ (Eq.trans l≡l₁₁++a++l₂' (Eq.sym (List.++-assoc _ ([ a ] ++ _) l₂)))) }
--   -- }
-- append {A} y₁ n₁@(suc n₁') l₁ (black t₁₁ a t₁₂) y₂ n₂ l₂ t₂ =
--   bind (F (Σ++ color λ y → Σ++ nat λ n → prod⁺ (U (meta (n ≤ (bound y₁ n₁ n₂)))) (irbt A y n (l₁ ++ l₂))))
--     (append _ _ _ t₁₂ _ _ _ t₂)
--     λ { (y , n , p , t₂') →
--       bind (F (Σ++ color λ y → Σ++ nat λ n → prod⁺ (U (meta (n ≤ (bound y₁ n₁ n₂)))) (irbt A y n (l₁ ++ l₂))))
--         (i-join _ _ _ t₁₁ a _ _ _ t₂')
--         (λ { (y₂' , l , l≡l₁₁++a++l₂' , inj₁ t₂) → ret (y₂' , 1 + (n₁' Nat.⊔ n) , {!   !} , {!   !})
--            ; (y₂' , l , l≡l₁₁++a++l₂' , inj₂ t₂) → ret (y₂' , n₁' Nat.⊔ n , {!   !} , {!   !})
--           })
--     }
--   -- step (F (rbt A (l₁ ++ l₂))) 1 $
--   -- bind (F (rbt A (l₁ ++ l₂))) (append _ _ _ t₁₂ _ _ _ t₂) λ { ⟪ t₂' ⟫ →
--   -- bind (F (rbt A (l₁ ++ l₂)))  (i-join _ _ _ t₁₁ a _ _ _ t₂')
--   --   λ { (_ , l , l≡l₁₁++a++l₂' , inj₁ t₂) →
--   --       ret (mk ⟪ t₂ ⟫ (Eq.trans l≡l₁₁++a++l₂' (Eq.sym (List.++-assoc _ ([ a ] ++ _) l₂))))
--   --     ; (_ , l , l≡l₁₁++a++l₂' , inj₂ t₂) →
--   --       ret (mk ⟪ t₂ ⟫ (Eq.trans l≡l₁₁++a++l₂' (Eq.sym (List.++-assoc _ ([ a ] ++ _) l₂)))) }
--   -- }

-- -- append/is-bounded : ∀ {A} y₁ n₁ l₁ t₁ y₂ n₂ l₂ t₂ → IsBounded (rbt A (l₁ ++ l₂)) (append y₁ n₁ l₁ t₁ y₂ n₂ l₂ t₂) (1 + (4 * (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂)))
-- -- append/is-bounded {A} .black .zero .[] leaf y₂ n₂ l₂ t₂ = bound/relax (λ u → Nat.z≤n) bound/ret
-- -- append/is-bounded {A} .red n₁ l₁ (red {l₁ = l₁₁} {l₂ = l₁₂} t₁₁ a t₁₂) y₂ n₂ l₂ t₂ = {!   !}
-- --   -- Eq.subst
-- --     -- (IsBounded _ _) {x = 1 + {!   !}}
-- --     -- {!   !}
-- --     -- (bound/step 1 {!   !}
-- --       -- (Eq.subst
-- --         -- (IsBounded _ _)
-- --         -- {!   !}
-- --         -- (bound/bind/const {!   !} {!   !} {!   !} {!   !})))
-- -- append/is-bounded {A} .black .(suc _) .(_ ++ [ a ] ++ _) (black t₁ a t₃) y₂ n₂ l₂ t₂ = {!   !}


module _ (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) where
  open StrictTotalOrder Key

  𝕂 : tp pos
  𝕂 = U (meta (StrictTotalOrder.Carrier Key))
