{-# OPTIONS --rewriting #-}

open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.MergeSort (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid hiding (A)
open import Calf.Data.Product
open import Calf.Data.Bool
open import Calf.Data.Nat
open import Calf.Data.List using (list; []; _∷_; _∷ʳ_; [_]; length; _++_; reverse)
open import Calf.Data.Equality using (_≡_; refl)
open import Calf.Data.IsBoundedG costMonoid
open import Calf.Data.IsBounded costMonoid
open import Calf.Data.BigO costMonoid

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as N
open import Data.Nat.Square
open import Data.Nat.Log2


open import Examples.Sorting.Sequential.MergeSort.Split M public
open import Examples.Sorting.Sequential.MergeSort.Merge M public

sort/clocked : cmp $ Π nat λ k → Π (list A) λ l → Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) λ _ → F (sort-result l)
sort/clocked zero    l h = ret (l , refl , short-sorted (⌈log₂n⌉≡0⇒n≤1 (N.n≤0⇒n≡0 h)))
sort/clocked (suc k) l h =
  bind (F (sort-result l)) (split l) λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) →
  let
    h₁ , h₂ =
      let open N.≤-Reasoning in
      (begin
        ⌈log₂ length l₁ ⌉
      ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
        ⌈log₂ ⌊ length l /2⌋ ⌉
      ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
        ⌈log₂ ⌈ length l /2⌉ ⌉
      ≤⟨ log₂-suc (length l) h ⟩
        k
      ∎) ,
      (begin
        ⌈log₂ length l₂ ⌉
      ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
        ⌈log₂ ⌈ length l /2⌉ ⌉
      ≤⟨ log₂-suc (length l) h ⟩
        k
      ∎)
  in
  bind (F (sort-result l)) (sort/clocked k l₁ h₁) λ (l₁' , l₁↭l₁' , sorted-l₁') →
  bind (F (sort-result l)) (sort/clocked k l₂ h₂) λ (l₂' , l₂↭l₂' , sorted-l₂') →
  bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
  ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)

sort/clocked/total : ∀ k l h → IsValuable (sort/clocked k l h)
sort/clocked/total zero    l h u = ↓ refl
sort/clocked/total (suc k) l h u rewrite Valuable.proof (split/total l u) = ↓
  let
    ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) = Valuable.value (split/total l u)
    h₁ , h₂ =
      let open N.≤-Reasoning in
      (begin
        ⌈log₂ length l₁ ⌉
      ≡⟨ Eq.cong ⌈log₂_⌉ length₁ ⟩
        ⌈log₂ ⌊ length l /2⌋ ⌉
      ≤⟨ log₂-mono (N.⌊n/2⌋≤⌈n/2⌉ (length l)) ⟩
        ⌈log₂ ⌈ length l /2⌉ ⌉
      ≤⟨ log₂-suc (length l) h ⟩
        k
      ∎) ,
      (begin
        ⌈log₂ length l₂ ⌉
      ≡⟨ Eq.cong ⌈log₂_⌉ length₂ ⟩
        ⌈log₂ ⌈ length l /2⌉ ⌉
      ≤⟨ log₂-suc (length l) h ⟩
        k
      ∎)
    (l₁' , l₁↭l₁' , sorted-l₁') = Valuable.value (sort/clocked/total k l₁ h₁ u)
    (l₂' , l₂↭l₂' , sorted-l₂') = Valuable.value (sort/clocked/total k l₂ h₂ u)
  in
  let open ≡-Reasoning in
  begin
    ( bind (F (sort-result l)) (sort/clocked k l₁ h₁) λ (l₁' , l₁↭l₁' , sorted-l₁') →
      bind (F (sort-result l)) (sort/clocked k l₂ h₂) λ (l₂' , l₂↭l₂' , sorted-l₂') →
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)
    )
  ≡⟨
    Eq.cong
      (λ e →
        bind (F (sort-result l)) e λ (l₁' , l₁↭l₁' , sorted-l₁') →
        bind (F (sort-result l)) (sort/clocked k l₂ h₂) λ (l₂' , l₂↭l₂' , sorted-l₂') →
        bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
        ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)
      )
      (Valuable.proof (sort/clocked/total k l₁ h₁ u))
  ⟩
    ( bind (F (sort-result l)) (sort/clocked k l₂ h₂) λ (l₂' , l₂↭l₂' , sorted-l₂') →
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)
    )
  ≡⟨
    Eq.cong
      (λ e →
        bind (F (sort-result l)) e λ (l₂' , l₂↭l₂' , sorted-l₂') →
        bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
        ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)
      )
      (Valuable.proof (sort/clocked/total k l₂ h₂ u))
  ⟩
    ( bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)
    )
  ≡⟨
    Eq.cong
      (λ e →
        bind (F (sort-result l)) e λ (l' , l₁'++l₂'↭l , l'-sorted) →
        ret (l' , trans l↭l₁++l₂ (trans (++⁺-↭ l₁↭l₁' l₂↭l₂') l₁'++l₂'↭l) , l'-sorted)
      )
      (Valuable.proof (merge/total (l₁' , l₂') (sorted-l₁' , sorted-l₂') u))
  ⟩
    ret _
  ∎

sort/clocked/cost : cmp $ Π nat λ k → Π (list A) λ l → Π (meta⁺ (⌈log₂ length l ⌉ Nat.≤ k)) λ _ → F unit
sort/clocked/cost k l _ = step⋆ (k * length l)

sort/clocked/is-bounded : ∀ k l h → IsBoundedG (sort-result l) (sort/clocked k l h) (sort/clocked/cost k l h)
sort/clocked/is-bounded zero    l h = ≤⁻-refl
sort/clocked/is-bounded (suc k) l h =
  bound/bind/const
    {e = split l}
    {f = λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) →
      bind (F (sort-result l)) (sort/clocked k l₁ _) λ (l₁' , l₁↭l₁' , sorted-l₁') →
      bind (F (sort-result l)) (sort/clocked k l₂ _) λ (l₂' , l₂↭l₂' , sorted-l₂') →
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret {sort-result l} (l' , ↭-trans l↭l₁++l₂ (↭-trans (_↭_.trans (++⁺ʳ-↭ l₂ l₁↭l₁') (++⁺ˡ-↭ l₁' l₂↭l₂')) (↭-trans l₁'++l₂'↭l _↭_.refl)) , l'-sorted)
    }
    0
    (suc k * length l)
    (split/is-bounded l)
    λ ((l₁ , l₂) , length₁ , length₂ , l↭l₁++l₂) →
  Eq.subst
    (IsBounded (sort-result l) $
      bind (F (sort-result l)) (sort/clocked k l₁ _) λ (l₁' , l₁↭l₁' , sorted-l₁') →
      bind (F (sort-result l)) (sort/clocked k l₂ _) λ (l₂' , l₂↭l₂' , sorted-l₂') →
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret {sort-result l} (l' , ↭-trans l↭l₁++l₂ (↭-trans (_↭_.trans (++⁺ʳ-↭ l₂ l₁↭l₁') (++⁺ˡ-↭ l₁' l₂↭l₂')) (↭-trans l₁'++l₂'↭l _↭_.refl)) , l'-sorted)
    )
    (let open ≡-Reasoning in
    begin
      k * length l₁ + (k * length l₂ + (length l₁ + length l₂))
    ≡˘⟨ N.+-assoc (k * length l₁) (k * length l₂) (length l₁ + length l₂) ⟩
      (k * length l₁ + k * length l₂) + (length l₁ + length l₂)
    ≡˘⟨ Eq.cong (_+ (length l₁ + length l₂)) (N.*-distribˡ-+ k (length l₁) (length l₂)) ⟩
      k * (length l₁ + length l₂) + (length l₁ + length l₂)
    ≡˘⟨ N.+-comm (length l₁ + length l₂) (k * (length l₁ + length l₂)) ⟩
      suc k * (length l₁ + length l₂)
    ≡˘⟨ Eq.cong (suc k *_) (length-++ l₁) ⟩
      suc k * (length (l₁ ++ l₂))
    ≡˘⟨ Eq.cong (suc k *_) (↭-length l↭l₁++l₂) ⟩
      suc k * length l
    ∎) $
  bound/bind/const
    {e = sort/clocked k l₁ _}
    {f = λ (l₁' , l₁↭l₁' , sorted-l₁') →
      bind (F (sort-result l)) (sort/clocked k l₂ _) λ (l₂' , l₂↭l₂' , sorted-l₂') →
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret {sort-result l} (l' , ↭-trans l↭l₁++l₂ (↭-trans (_↭_.trans (++⁺ʳ-↭ l₂ l₁↭l₁') (++⁺ˡ-↭ l₁' l₂↭l₂')) (↭-trans l₁'++l₂'↭l _↭_.refl)) , l'-sorted)
    }
    (k * length l₁)
    (k * length l₂ + (length l₁ + length l₂))
    (sort/clocked/is-bounded k l₁ _)
    λ (l₁' , l₁↭l₁' , sorted-l₁') →
  bound/bind/const
    {e = sort/clocked k l₂ _}
    {f = λ (l₂' , l₂↭l₂' , sorted-l₂') →
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret {sort-result l} (l' , ↭-trans l↭l₁++l₂ (↭-trans (_↭_.trans (++⁺ʳ-↭ l₂ l₁↭l₁') (++⁺ˡ-↭ l₁' l₂↭l₂')) (↭-trans l₁'++l₂'↭l _↭_.refl)) , l'-sorted)
    }
    (k * length l₂)
    (length l₁ + length l₂)
    (sort/clocked/is-bounded k l₂ _)
    λ (l₂' , l₂↭l₂' , sorted-l₂') →
  Eq.subst
    (IsBounded (sort-result l) $
      bind (F (sort-result l)) (merge (l₁' , l₂') (sorted-l₁' , sorted-l₂')) λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret {sort-result l} (l' , ↭-trans l↭l₁++l₂ (↭-trans (_↭_.trans (++⁺ʳ-↭ l₂ l₁↭l₁') (++⁺ˡ-↭ l₁' l₂↭l₂')) (↭-trans l₁'++l₂'↭l _↭_.refl)) , l'-sorted)
    )
    (let open ≡-Reasoning in
    begin
      length l₁' + length l₂' + 0
    ≡⟨ N.+-identityʳ (length l₁' + length l₂') ⟩
      length l₁' + length l₂'
    ≡˘⟨ Eq.cong₂ _+_ (↭-length l₁↭l₁') (↭-length l₂↭l₂') ⟩
      length l₁ + length l₂
    ∎) $
  bound/bind/const {B = sort-result l}
    {e = merge (l₁' , l₂') _}
    {f = λ (l' , l₁'++l₂'↭l , l'-sorted) →
      ret {sort-result l} (l' , ↭-trans l↭l₁++l₂ (↭-trans (_↭_.trans (++⁺ʳ-↭ l₂ l₁↭l₁') (++⁺ˡ-↭ l₁' l₂↭l₂')) (↭-trans l₁'++l₂'↭l _↭_.refl)) , l'-sorted)}
    (length l₁' + length l₂')
    0
    (merge/is-bounded (l₁' , l₂') _)
    λ _ →
  ≤⁻-refl


sort : cmp (Π (list A) λ l → F (sort-result l))
sort l = sort/clocked ⌈log₂ length l ⌉ l N.≤-refl

sort/total : IsTotal sort
sort/total l = sort/clocked/total ⌈log₂ length l ⌉ l N.≤-refl

sort/cost : cmp (Π (list A) λ _ → cost)
sort/cost l = sort/clocked/cost ⌈log₂ length l ⌉ l N.≤-refl

sort/is-bounded : ∀ l → IsBoundedG (sort-result l) (sort l) (sort/cost l)
sort/is-bounded l = sort/clocked/is-bounded ⌈log₂ length l ⌉ l N.≤-refl

sort/asymptotic : given (list A) measured-via length , sort ∈𝓞(λ n → n * ⌈log₂ n ⌉)
sort/asymptotic = f[n]≤g[n]via λ l →
  Eq.subst
    (IsBounded (sort-result l) (sort l))
    (N.*-comm ⌈log₂ length l ⌉ (length l))
    (sort/is-bounded l)
