{-# OPTIONS --rewriting #-}

open import Algebra.Cost
open import Data.Nat using (ℕ)
open import Examples.Sorting.Comparable

module Examples.Sorting.Core
  (costMonoid : CostMonoid) (fromℕ : ℕ → CostMonoid.ℂ costMonoid)
  (M : Comparable costMonoid fromℕ)
  where

open Comparable M

open import Calf costMonoid hiding (A)
open import Calf.Data.Product using (_×⁺_)
open import Calf.Data.List using (list; []; _∷_; _∷ʳ_; [_]; length; _++_; reverse)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat as Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _*_; _^_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as N

open import Data.List.Properties using (++-assoc; length-++) public

open import Data.List.Relation.Binary.Permutation.Propositional public
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (↭-length; ¬x∷xs↭[]; All-resp-↭; Any-resp-↭; drop-∷; ++-identityʳ)
  renaming (++-comm to ++-comm-↭; ++⁺ˡ to ++⁺ˡ-↭; ++⁺ʳ to ++⁺ʳ-↭; ++⁺ to ++⁺-↭) public

open import Data.List.Relation.Unary.All using (All; []; _∷_; map; lookup) public
open import Data.List.Relation.Unary.All.Properties as AllP using () renaming (++⁺ to ++⁺-All) public
open import Data.List.Relation.Unary.Any using (Any; here; there)


_≤*_ : val A → val (list A) → Set
_≤*_ x = All (x ≤_)

≤-≤* : ∀ {x₁ x₂ l} → x₁ ≤ x₂ → x₂ ≤* l → x₁ ≤* l
≤-≤* x₁≤x₂ = map (≤-trans x₁≤x₂)

data Sorted : val (list A) → Set where
  [] : Sorted []
  _∷_ : ∀ {y ys} → y ≤* ys → Sorted ys → Sorted (y ∷ ys)

sorted : val (list A) → tp⁺
sorted l = meta⁺ (Sorted l)

short-sorted : {l : val (list A)} → length l Nat.≤ 1 → Sorted l
short-sorted {[]} _ = []
short-sorted {_ ∷ []} _ = [] ∷ []
short-sorted {_ ∷ _ ∷ _} (s≤s ())

unique-sorted : ∀ {l'₁ l'₂} → Sorted l'₁ → Sorted l'₂ → l'₁ ↭ l'₂ → l'₁ ≡ l'₂
unique-sorted []             []             ↭ = refl
unique-sorted []             (h₂ ∷ sorted₂) ↭ = contradiction (↭-sym ↭) ¬x∷xs↭[]
unique-sorted (h₁ ∷ sorted₁) []             ↭ = contradiction (↭) ¬x∷xs↭[]
unique-sorted (h₁ ∷ sorted₁) (h₂ ∷ sorted₂) ↭ with
  ≤-antisym
    (lookup (≤-refl ∷ h₁) (Any-resp-↭ (↭-sym ↭) (here refl)))
    (lookup (≤-refl ∷ h₂) (Any-resp-↭ (↭) (here refl)))
... | refl = Eq.cong (_ ∷_) (unique-sorted sorted₁ sorted₂ (drop-∷ ↭))

join-sorted : ∀ {l₁ mid l₂} → Sorted l₁ → Sorted l₂ → All (_≤ mid) l₁ → All (mid ≤_) l₂ → Sorted (l₁ ++ [ mid ] ++ l₂)
join-sorted []            sorted₂ all₁        all₂ = all₂ ∷ sorted₂
join-sorted (h ∷ sorted₁) sorted₂ (h' ∷ all₁) all₂ =
  ++⁺-All h (h' ∷ ≤-≤* h' all₂) ∷ (join-sorted sorted₁ sorted₂ all₁ all₂)

++⁻ˡ : ∀ xs {ys} → Sorted (xs ++ ys) → Sorted xs
++⁻ˡ []       sorted       = []
++⁻ˡ (x ∷ xs) (h ∷ sorted) = AllP.++⁻ˡ xs h ∷ (++⁻ˡ xs sorted)

++⁻ʳ : ∀ xs {ys} → Sorted (xs ++ ys) → Sorted ys
++⁻ʳ []       sorted       = sorted
++⁻ʳ (x ∷ xs) (h ∷ sorted) = ++⁻ʳ xs sorted

split-sorted₁ : ∀ xs {x} → Sorted (xs ∷ʳ x) → All (_≤ x) xs
split-sorted₁ []       sorted       = []
split-sorted₁ (x ∷ xs) (h ∷ sorted) = proj₂ (AllP.∷ʳ⁻ h) ∷ split-sorted₁ xs sorted

uncons₁ : ∀ {x xs} → Sorted (x ∷ xs) → x ≤* xs
uncons₁ (h ∷ sorted) = h

uncons₂ : ∀ {x xs} → Sorted (x ∷ xs) → Sorted xs
uncons₂ (h ∷ sorted) = sorted

sorted-of : val (list A) → val (list A) → tp⁺
sorted-of l l' = meta⁺ (l ↭ l') ×⁺ (sorted l')

sort-result : val (list A) → tp⁺
sort-result l = Σ⁺ (list A) (sorted-of l)

sorting : tp⁻
sorting = Π (list A) λ l → F (sort-result l)

record Valuable {A : tp⁺} (e : cmp (F A)) : Set where
  constructor ↓_
  field
    {value} : val A
    proof : e ≡ ret value

IsValuable : {A : tp⁺} → cmp (F A) → Set
IsValuable e = ◯ (Valuable e)

IsTotal : cmp sorting → Set
IsTotal sort = (l : val (list A)) → IsValuable (sort l)

-- discard proofs, which may be different
_algorithm : cmp sorting → cmp (Π (list A) λ _ → F (list A))
_algorithm sort l = bind (F (list A)) (sort l) λ (l' , _) → ret l'

IsSort⇒≡ : ∀ sort₁ → IsTotal sort₁ → ∀ sort₂ → IsTotal sort₂ → ◯ (sort₁ algorithm ≡ sort₂ algorithm)
IsSort⇒≡ sort₁ total₁ sort₂ total₂ u =
  funext λ l →
    let (l₁' , l↭l₁' , sorted₁) = Valuable.value (total₁ l u) in
    let (l₂' , l↭l₂' , sorted₂) = Valuable.value (total₂ l u) in
    begin
      (sort₁ algorithm) l
    ≡⟨ Eq.cong (λ e → bind (F (list A)) e λ (l' , _) → ret l') (Valuable.proof (total₁ l u)) ⟩
      ret l₁'
    ≡⟨ Eq.cong ret (unique-sorted sorted₁ sorted₂ (trans (↭-sym l↭l₁') l↭l₂')) ⟩
      ret l₂'
    ≡˘⟨ Eq.cong (λ e → bind (F (list A)) e λ (l' , _) → ret l') (Valuable.proof (total₂ l u)) ⟩
      (sort₂ algorithm) l
    ∎
      where open ≡-Reasoning
