module 1Lab.Set.Pi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.CartesianKanOps

-- The following two proofs are imported from the 1Lab: https://1lab.dev/1Lab.Set.Pi.html
funext-dep
  : ∀ {A : I → Set} {B : (i : I) → A i → Set} {f g}
  → ( ∀ {x₀ x₁} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁) )
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep {A = A} {B} h i x =
  transp (λ k → B i (coei→i A i x k)) (i ∨ ~ i)
    (h (λ j → coei→j A i j x) i)

funext-dep-i0
  : ∀ {A : I → Set} {B : (i : I) → A i → Set} {f g}
  → ( ∀ (x : A i0)
    → PathP (λ i → B i (coe0→i A i x)) (f x) (g (coe0→1 A x)))
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep-i0 {A = A} {B} {f} {g} h =
  funext-dep λ {x₀} {x₁} p →
  subst (λ (p : (i : I) → A i) → PathP (λ i → B i (p i)) (f (p i0)) (g (p i1)))
    (λ j i → coePath A (λ i → p i) i0 i j)
    (h x₀)
