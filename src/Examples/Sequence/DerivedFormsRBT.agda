{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence.DerivedFormsRBT where

open import Examples.Sequence.RedBlackTree

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid

open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Product
open import Calf.Types.Sum
open import Calf.Types.Bounded costMonoid
open import Data.Product hiding (map)
open import Data.List as List hiding (sum; map)
import Data.List.Properties as List
open import Data.Nat as Nat using (_+_; _*_; _<_; _>_; _≤ᵇ_; _<ᵇ_; ⌊_/2⌋; _≡ᵇ_; _≥_; _∸_)
import Data.Nat.Properties as Nat
open import Data.Nat.Logarithm

open import Level using (0ℓ)
open import Function using (_$_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning; ≢-sym)


module Sum where
  sum/seq : cmp $
    Π color λ y → Π nat λ n → Π (list nat) λ l → Π (irbt nat y n l) λ _ → F nat
  sum/seq .black .zero .[] leaf = ret 0
  sum/seq .red n .(_ ++ [ a ] ++ _) (red t₁ a t₂) =
    step (F nat) (1 , 1) $
      bind (F (nat)) ((sum/seq _ _ _ t₁) & (sum/seq _ _ _ t₂))
      (λ (s₁ , s₂) → ret (s₁ + a + s₂))
  sum/seq .black .(suc _) .(_ ++ [ a ] ++ _) (black t₁ a t₂) =
    step (F nat) (1 , 1) $
      bind (F (nat)) ((sum/seq _ _ _ t₁) & (sum/seq _ _ _ t₂))
      (λ (s₁ , s₂) → ret (s₁ + a + s₂))

  span/sum : val color → val nat → val nat
  span/sum red n = 1 + 2 * n
  span/sum black n = 2 * n

  span/bounded : ∀ y n → (span/sum y n) Nat.≤ (1 + 2 * n)
  span/bounded red n = Nat.≤-refl
  span/bounded black n = Nat.n≤1+n (2 * n)

  sum/bounded' : ∀ y n l t → IsBounded nat (sum/seq y n l t) (List.length l , span/sum y n)
  sum/bounded' .black .zero .[] leaf = bound/relax (λ x → Nat.z≤n , Nat.z≤n) bound/ret
  sum/bounded' .red n l (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    Eq.subst
      (IsBounded _ _) {y = List.length l , 1 + 2 * n}
        (begin
          (1 , 1) ⊕ (length l₁ + length l₂ , n + (n + zero))
        ≡⟨⟩
          (1 + (length l₁ + length l₂) , 1 + (n + (n + zero)))
        ≡˘⟨ Eq.cong₂ _,_ (Nat.+-assoc 1 (length l₁) (length l₂)) refl ⟩
          (1 + length l₁ + length l₂ , suc (n + (n + zero)))
        ≡⟨ Eq.cong₂ _,_ (Eq.cong₂ _+_ (Nat.+-comm 1 (length l₁)) refl) refl ⟩
          (length l₁ + 1 + length l₂ , suc (n + (n + zero)))
        ≡⟨ Eq.cong₂ _,_ (Nat.+-assoc (length l₁) 1 (length l₂)) refl ⟩
          (length l₁ + (1 + length l₂) , suc (n + (n + zero)))
        ≡⟨⟩
          (length l₁ + length (a ∷ l₂) , suc (n + (n + zero)))
        ≡˘⟨ Eq.cong₂ _,_ (List.length-++ l₁) refl ⟩
          (length (l₁ ++ a ∷ l₂) , suc (n + (n + zero)))
        ∎)
      (bound/step (1 , 1) (List.length l₁ + List.length l₂  , 2 * n)
        (Eq.subst
          (IsBounded _ _) {x = List.length l₁ + List.length l₂ + 0 , 2 * n + 0}
          (Eq.cong₂ _,_ (Nat.+-identityʳ (List.length l₁ + List.length l₂)) (Nat.+-identityʳ (2 * n)))
          (bound/bind/const
            (List.length l₁ + List.length l₂  , 2 * n)
            𝟘
            (Eq.subst
              (IsBounded _ _)
              (Eq.cong₂ _,_ refl (Nat.⊔-idem (2 * n)))
              (bound/par (sum/bounded' _ _ _ t₁) (sum/bounded' _ _ _ t₂)))
            (λ _ → bound/ret)))
      )
        where open ≡-Reasoning
  sum/bounded' .black n@(suc n') l (black {y₁ = y₁} {y₂ = y₂} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    Eq.subst
      (IsBounded _ _) {y = List.length l , 2 * (suc n') }
        (begin
          (1 , 1) ⊕ (length l₁ + length l₂ , suc (n' + (n' + zero)))
        ≡⟨⟩
          (1 + (length l₁ + length l₂) , suc (suc (n' + (n' + zero))))
        ≡˘⟨ Eq.cong₂ _,_ (Nat.+-assoc 1 (length l₁) (length l₂)) (Eq.cong suc (Eq.cong₂ _+_ (Nat.+-comm n' 1) refl)) ⟩
          (1 + length l₁ + length l₂ , suc (n' + 1 + (n' + zero)))
        ≡⟨ Eq.cong₂ _,_ (Eq.cong₂ _+_ (Nat.+-comm 1 (length l₁)) refl) (Eq.cong suc (Nat.+-assoc n' 1 (n' + zero))) ⟩
          (length l₁ + 1 + length l₂ , suc (n' + (1 + (n' + zero))))
        ≡⟨ Eq.cong₂ _,_ (Nat.+-assoc (length l₁) 1 (length l₂)) refl ⟩
          (length l₁ + (1 + length l₂) , suc (n' + (1 + (n' + zero))))
        ≡⟨⟩
          (length l₁ + length (a ∷ l₂) , suc (n' + (1 + (n' + 0))))
        ≡˘⟨ Eq.cong₂ _,_ (List.length-++ l₁) refl ⟩
          (length (l₁ ++ a ∷ l₂) , suc (n' + suc (n' + zero)))
        ∎)
      (bound/step (1 , 1) (List.length l₁ + List.length l₂ ,  1 + 2 * n')
        (Eq.subst
          (IsBounded _ _)  {x = List.length l₁ + List.length l₂ + 0 , 1 + 2 * n' + 0}
          (Eq.cong₂ _,_ (Nat.+-identityʳ (List.length l₁ + List.length l₂)) (Nat.+-identityʳ (1 + 2 * n')))
          (bound/bind/const (List.length l₁ + List.length l₂ , 1 + 2 * n') 𝟘
            (Eq.subst
              (IsBounded _ _)
              (Eq.cong₂ _,_ refl (Nat.⊔-idem (1 + 2 * n')))
              (bound/par
                (bound/relax (λ u → Nat.≤-refl , (span/bounded y₁ n')) (sum/bounded' _ _ _ t₁))
                (bound/relax (λ u → Nat.≤-refl , (span/bounded y₂ n')) (sum/bounded' _ _ _ t₂))))
            (λ a₁ → bound/ret))))
        where open ≡-Reasoning

  sum/bounded : ∀ y n l t → IsBounded nat (sum/seq y n l t) (length l , 1 + 2 * ⌈log₂ (1 + length l) ⌉)
  sum/bounded y n l t = bound/relax (λ u → Nat.≤-refl , lemma) (sum/bounded' y n l t)
    where
      open Nat.≤-Reasoning

      lemma : span/sum y n Nat.≤ suc (2 * ⌈log₂ (1 + length l) ⌉)
      lemma =
        begin
          span/sum y n
        ≤⟨ span/bounded y n ⟩
          suc (2 * n)
        ≤⟨ Nat.s≤s (Nat.*-monoʳ-≤ 2 (i-nodes/bound/log-node-black-height t)) ⟩
          suc (2 * ⌈log₂ (1 + i-nodes t) ⌉)
        ≡⟨ Eq.cong (λ x → suc (2 * ⌈log₂ (1 + x) ⌉)) (i-nodes≡lengthl t) ⟩
          suc (2 * ⌈log₂ (1 + length l) ⌉)
        ∎


module Map {A B : tp pos} (f : val A → val B) where
  map :
    cmp (
      Π color λ y₁ → Π nat λ n₁ → Π (list A) λ l₁ → Π (irbt A y₁ n₁ l₁) λ _ →
      F (Σ++ color λ y → Σ++ nat λ n → Σ++ (list B) λ l → prod⁺ (prod⁺ (prod⁺ (U (meta (n Nat.≥ n₁))) (U (meta (n Nat.≤ (1 + n₁))))) (U (meta (List.length l ≡ List.length l₁)))) (irbt B y n l))
    )
  map .black .zero .[] leaf =
    ret (black , (0 , ([] , (((Nat.z≤n , Nat.z≤n) , refl) , leaf))))
  map .red n'₁ l (red {n = n} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    bind
      (F (Σ++ color λ y → Σ++ nat λ n → Σ++ (list B) λ l → prod⁺ (prod⁺ (prod⁺ (U (meta (n Nat.≥ n'₁))) (U (meta (n Nat.≤ (1 + n'₁))))) (U (meta (List.length l ≡ List.length (l₁ ++ a ∷ l₂))))) (irbt B y n l)))
      (map black n l₁ t₁ & map black n l₂ t₂)
      λ ((y₁ , n₁ , l'₁ , ((p₁ , q₁) , t₁) , s₁) , (y₂ , n₂ , l'₂ , ((p₂ , q₂) , t₂) , s₂)) →
        bind
          ((F (Σ++ color λ y → Σ++ nat λ n → Σ++ (list B) λ l → prod⁺ (prod⁺ (prod⁺ (U (meta (n Nat.≥ n'₁))) (U (meta (n Nat.≤ (1 + n'₁))))) (U (meta (List.length l ≡ List.length (l₁ ++ a ∷ l₂))))) (irbt B y n l))))
          (i-join _ _ _ s₁ (f a) _ _ _ s₂)
          λ { (y , l , p , inj₁ t') →  {!   !}
          -- ret (y , 1 + (n₁ Nat.⊔ n₂) , l , (({!   !} , {!   !}) , {!   !}) , t')
            ; (y , l , p , inj₂ t') → {!   !}
            -- ret (y , n₁ Nat.⊔ n₂ , l , (({!   !} , {!   !}) , {!   !}) , t')
            }
  map .black n'₁@(suc n) l (black {y₁ = y₁} {y₂ = y₂} {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    bind
      (F (Σ++ color λ y → Σ++ nat λ n → Σ++ (list B) λ l → prod⁺ (prod⁺ (prod⁺ (U (meta (n Nat.≥ n'₁))) (U (meta (n Nat.≤ (1 + n'₁))))) (U (meta (List.length l ≡ List.length (l₁ ++ a ∷ l₂))))) (irbt B y n l)))
      (map y₁ n l₁ t₁ & map y₂ n l₂ t₂)
      λ ((y₁ , n₁ , l'₁ , ((p₁ , q₁) , t₁) , s₁) , (y₂ , n₂ , l'₂ , ((p₂ , q₂) , t₂) , s₂)) →
        bind
          ((F (Σ++ color λ y → Σ++ nat λ n → Σ++ (list B) λ l → prod⁺ (prod⁺ (prod⁺ (U (meta (n Nat.≥ n'₁))) (U (meta (n Nat.≤ (1 + n'₁))))) (U (meta (List.length l ≡ List.length (l₁ ++ a ∷ l₂))))) (irbt B y n l))))
          (i-join _ _ _ s₁ (f a) _ _ _ s₂)
          λ { (y , l , p , inj₁ t') → ret (y , 1 + (n₁ Nat.⊔ n₂) , l , {!   !} , t')
            ; (y , l , p , inj₂ t') → ret (y , n₁ Nat.⊔ n₂ , l , {!   !} , t')
            }

  lemma : (n : val nat) → (n₁ : val nat) → (n₂ : val nat) → n₁ Nat.≥ n → n₁ Nat.≤ (1 + n) → n₂ Nat.≥ n → n₂ Nat.≤ (1 + n) → (n₁ Nat.⊔ n₂ ∸ n₁ Nat.⊓ n₂) Nat.≤ 1
  lemma n n₁ n₂ p₁ p₂ p₃ p₄ with n₁ Nat.≟ n | n₂ Nat.≟ n
  ... | yes refl | yes refl =
    Nat.≤-trans (Nat.≤-reflexive (Eq.subst (λ t → t ∸ n Nat.⊓ n ≡ 0) (Eq.sym (Nat.⊔-idem n)) (Eq.subst (λ t → n ∸ t ≡ 0) (Eq.sym (Nat.⊓-idem n)) (Nat.n∸n≡0 n)))) Nat.z≤n
  ... | yes refl | no p = {!   !}
  ... | no p | yes refl = {!   !}
  ... | no p₁ | no p₂ =
    Eq.subst (λ 1+n → 1+n ∸ n₁ Nat.⊓ n₂ Nat.≤ 1) {!   !} (Eq.subst (λ 1+n → (1 + n) ∸ 1+n Nat.≤ 1) {!   !} (Nat.≤-trans (Nat.≤-reflexive (Nat.n∸n≡0 (1 + n))) Nat.z≤n))


  span/map : val color → val nat → val nat
  span/map red n = 4 + 8 * n
  span/map black n = 8 * n

  map/is-bounded : ∀ y₁ n₁ l₁ t →
    IsBounded
      ((Σ++ color λ y → Σ++ nat λ n → Σ++ (list B) λ l → prod⁺ (prod⁺ (prod⁺ (U (meta (n Nat.≥ n₁))) (U (meta (n Nat.≤ (1 + n₁))))) (U (meta (List.length l ≡ List.length l₁)))) (irbt B y n l)))
      (map y₁ n₁ l₁ t) ((4 * List.length l₁) , span/map y₁ n₁)
  map/is-bounded .black .zero .[] leaf =
    bound/relax (λ u → Nat.z≤n , Nat.z≤n) bound/ret
  map/is-bounded .red n l (red {l₁ = l₁} {l₂ = l₂} t₁ a t₂) =
    Eq.subst
      (IsBounded _ _) {x = 1 + (4 * List.length l₁ + 4 * List.length l₂ + 3) , {!   !} }
      {!   !}
      (bound/step (1 , 1) (4 * List.length l₁ + 4 * List.length l₂ + 3 , 3 + 8 * n)
        (Eq.subst
          (IsBounded _ _) {y = 4 * List.length l₁ + 4 * List.length l₂ + 3 , {!  2 + 8 * n !}}
          {!   !}
          (bound/bind/const (4 * List.length l₁ + 4 * List.length l₂ , {!   !}) (3 , 3) (bound/par {!   !} {!   !}) {!   !})))
  map/is-bounded .black .(suc _) .(_ ++ [ a ] ++ _) (black t₁ a t₂) = {!   !}



module _ (Key : StrictTotalOrder 0ℓ 0ℓ 0ℓ) where
  open StrictTotalOrder Key

  𝕂 : tp pos
  𝕂 = U (meta (StrictTotalOrder.Carrier Key))
