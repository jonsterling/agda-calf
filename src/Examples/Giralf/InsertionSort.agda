module Examples.Giralf.InsertionSort where

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Nat.Properties as Nat
open import Cubical.Relation.Nullary

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Nat using (ℕ₌)
open import Calf.Computation.CList1
open import Calf.Computation.CList2
open import Calf.Computation.Debit
open import Calf.Computation.Product
open import Calf.Giralf

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with ≤Dec m n
... | yes p = true
... | no ¬p = false

insert : ∀ p → ℕ → CList₁ (1 +ℂ p) ℕ₌ , p ⊢ CList₁ p ℕ₌
insert p x =
  payᴳ (+ℂ-identityʳ p) $
  proj₁ᴳ {B = CList₁ p ℕ₌} $
  foldr₁ᴳ
    {A = (◁[ p ] CList₁ p ℕ₌) ×ᶜ CList₁ p ℕ₌}
    (pairᴳ
      (getᴳ p (+ℂ-identityʳ p) (cons₁ᴳ (+ℂ-identityʳ p) x nil₁ᴳ))
      nil₁ᴳ
    )
    (λ y →
      spendᴳ 1 refl $
      pairᴳ
        ( getᴳ p refl $
          if x ≤ᵇ y
            then cons₁ᴳ refl x (cons₁ᴳ (+ℂ-identityʳ p) y (proj₂ᴳ {A = ◁[ p ] CList₁ p ℕ₌} (idᴳ refl)))
            else cons₁ᴳ refl y (payᴳ (+ℂ-identityʳ p) (proj₁ᴳ {B = CList₁ p ℕ₌} (idᴳ refl)))
        )
        (cons₁ᴳ (+ℂ-identityʳ p) y (proj₂ᴳ {A = ◁[ p ] CList₁ p ℕ₌} (idᴳ refl)))
    )
    (idᴳ refl)

isort : CList₂ 0 1 ℕ₌ , 0ℂ ⊢ CList₁ 0 ℕ₌
isort =
  foldr₂ᴳ
    (λ r → CList₁ r ℕ₌)
    (λ r → nil₁ᴳ)
    insert
    (idᴳ refl)
