open import Examples.Sorting.Sequential.Comparable

module Examples.Sorting.Sequential.MergeSort.Merge (M : Comparable) where

open Comparable M
open import Examples.Sorting.Sequential.Core M

open import Calf costMonoid
open import Calf.Types.Unit
open import Calf.Types.Product
open import Calf.Types.Bool
open import Calf.Types.Nat
open import Calf.Types.List
open import Calf.Types.Eq
open import Calf.Types.BoundedG costMonoid
open import Calf.Types.Bounded costMonoid

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Function
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_)
import Data.Nat.Properties as N


open import Examples.Sorting.Sequential.MergeSort.Split M


prep' : ∀ {x : val A} {xs} y {ys l} → x ∷ xs ++ ys ↭ l → x ∷ xs ++ y ∷ ys ↭ y ∷ l
prep' {x} {xs} y {ys} {l} h =
  let open PermutationReasoning in
  begin
    (x ∷ xs ++ y ∷ ys)
  ↭⟨ ++-comm-↭ (x ∷ xs) (y ∷ ys) ⟩
    (y ∷ ys ++ x ∷ xs)
  ≡⟨⟩
    y ∷ (ys ++ x ∷ xs)
  <⟨ ++-comm-↭ ys (x ∷ xs) ⟩
    y ∷ (x ∷ xs ++ ys)
  <⟨ h ⟩
    y ∷ l
  ∎

merge/type : val pair → tp pos
merge/type (l₁ , l₂) = Σ++ (list A) λ l → sorted-of (l₁ ++ l₂) l

merge/clocked : cmp $
  Π nat λ k → Π pair λ (l₁ , l₂) →
  Π (prod⁺ (sorted l₁) (sorted l₂)) λ _ →
  Π (meta⁺ (length l₁ + length l₂ ≡ k)) λ _ →
  F (merge/type (l₁ , l₂))
merge/clocked zero    ([]     , []    ) (sorted₁      , sorted₂     ) h = ret ([] , refl , [])
merge/clocked (suc k) ([]     , l₂    ) ([]           , sorted₂     ) h = ret (l₂ , refl , sorted₂)
merge/clocked (suc k) (x ∷ xs , []    ) (sorted₁      , sorted₂     ) h = ret (x ∷ xs , ++-identityʳ (x ∷ xs) , sorted₁)
merge/clocked (suc k) (x ∷ xs , y ∷ ys) (h₁ ∷ sorted₁ , h₂ ∷ sorted₂) h =
  bind (F (merge/type (x ∷ xs , y ∷ ys))) (x ≤? y) $ case-≤
    (λ x≤y →
      let h' = N.suc-injective h in
      bind (F (merge/type (x ∷ xs , y ∷ ys)))
        (merge/clocked k (xs , y ∷ ys) (sorted₁ , h₂ ∷ sorted₂) h') λ (l , l↭xs++y∷ys , l-sorted) →
        ret (x ∷ l , prep x l↭xs++y∷ys , All-resp-↭ l↭xs++y∷ys (++⁺-All h₁ (x≤y ∷ ≤-≤* x≤y h₂)) ∷ l-sorted)
    )
    (λ x≰y →
      let y≤x = ≰⇒≥ x≰y in
      let h' = Eq.trans (Eq.sym (N.+-suc (length xs) (length ys))) (N.suc-injective h) in
      bind (F (merge/type (x ∷ xs , y ∷ ys)))
        (merge/clocked k (x ∷ xs , ys) (h₁ ∷ sorted₁ , sorted₂) h') λ (l , l↭x∷xs++ys , l-sorted) →
        ret (y ∷ l , prep' y l↭x∷xs++ys , All-resp-↭ l↭x∷xs++ys (++⁺-All (y≤x ∷ ≤-≤* y≤x h₁) h₂) ∷ l-sorted)
    )

merge/clocked/total : ∀ k p s h → IsValuable (merge/clocked k p s h)
merge/clocked/total zero    ([]     , []    ) (sorted₁      , sorted₂     ) h u = ↓ refl
merge/clocked/total (suc k) ([]     , l₂    ) ([]           , sorted₂     ) h u = ↓ refl
merge/clocked/total (suc k) (x ∷ xs , []    ) (sorted₁      , sorted₂     ) h u = ↓ refl
merge/clocked/total (suc k) (x ∷ xs , y ∷ ys) (h₁ ∷ sorted₁ , h₂ ∷ sorted₂) h u with ≤?-total x y u
... | yes x≤y , ≡ret
  rewrite ≡ret
    | Valuable.proof (merge/clocked/total k (xs , y ∷ ys) (sorted₁ , h₂ ∷ sorted₂) (N.suc-injective h) u)
  = ↓ refl
... | no x≰y , ≡ret
  rewrite ≡ret
    | Valuable.proof (merge/clocked/total k (x ∷ xs , ys) (h₁ ∷ sorted₁ , sorted₂) (Eq.trans (Eq.sym (N.+-suc (length xs) (length ys))) (N.suc-injective h)) u)
  = ↓ refl

merge/clocked/cost : cmp $
  Π nat λ k → Π pair λ (l₁ , l₂) →
  Π (prod⁺ (sorted l₁) (sorted l₂)) λ _ →
  Π (meta⁺ (length l₁ + length l₂ ≡ k)) λ _ →
  F unit
merge/clocked/cost k _ _ _ = step⋆ k

merge/clocked/is-bounded : ∀ k p s h → IsBoundedG (merge/type p) (merge/clocked k p s h) (merge/clocked/cost k p s h)
merge/clocked/is-bounded zero    ([]     , []    ) (sorted₁      , sorted₂     ) h = ≲-refl
merge/clocked/is-bounded (suc k) ([]     , l₂    ) ([]           , sorted₂     ) h = step⋆-mono-≲ (z≤n {suc k})
merge/clocked/is-bounded (suc k) (x ∷ xs , []    ) (sorted₁      , []          ) h = step⋆-mono-≲ (z≤n {suc k})
merge/clocked/is-bounded (suc k) (x ∷ xs , y ∷ ys) (h₁ ∷ sorted₁ , h₂ ∷ sorted₂) h =
  bound/bind/const
    {e = x ≤? y}
    {f = case-≤ (λ _ → bind (F (merge/type (x ∷ xs , y ∷ ys))) (merge/clocked k (xs , y ∷ ys) _ _) _) _}
    1
    k
    (h-cost x y)
    λ { (yes p) → bind-mono-≲ (merge/clocked/is-bounded k (xs , y ∷ ys) _ _) (λ _ → ≲-refl)
      ; (no ¬p) → bind-mono-≲ (merge/clocked/is-bounded k (x ∷ xs , ys) _ _) (λ _ → ≲-refl)
      }


merge : cmp $
  Π pair λ (l₁ , l₂) →
  Π (prod⁺ (sorted l₁) (sorted l₂)) λ _ →
  F (merge/type (l₁ , l₂))
merge (l₁ , l₂) s = merge/clocked (length l₁ + length l₂) (l₁ , l₂) s refl

merge/total : ∀ p s → IsValuable (merge p s)
merge/total (l₁ , l₂) s = merge/clocked/total (length l₁ + length l₂) (l₁ , l₂) s refl

merge/cost : cmp $
  Π pair λ (l₁ , l₂) →
  Π (prod⁺ (sorted l₁) (sorted l₂)) λ _ →
  cost
merge/cost (l₁ , l₂) s = merge/clocked/cost (length l₁ + length l₂) (l₁ , l₂) s refl

merge/is-bounded : ∀ p s → IsBoundedG (merge/type p) (merge p s) (merge/cost p s)
merge/is-bounded (l₁ , l₂) s = merge/clocked/is-bounded (length l₁ + length l₂) (l₁ , l₂) s refl
