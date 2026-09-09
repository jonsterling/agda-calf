module Calf.Computation.Free where

open import Cubical.Data.Nat using (zero; suc)

open import Calf.Core.Monad
open import Calf.Value
open import Calf.Value.Product
open import Calf.Computation

opaque
  unfolding M

  F : 𝒱 → 𝒞
  F X .U = M ∥ X ∥ᴾ
  F X .is-preorder = isPreorder× isPreorderℂ isPreorderᴾ
  F X .charge c (c' , x) = c +ℂ c' , x
  F X .charge-0 {c , x} = cong (_, x) (+ℂ-identityˡ c)
  F X .charge-+ {c , x} {c₁} {c₂} = cong (_, x) (+ℂ-assoc c₁ c₂ c)

  ret : X → U (F X)
  ret x = retᴹ (ηᴾ x)

  bind : U (F X) → (X → U A) → U A
  bind {A = A} (c , x) k = rec (A .is-preorder) (A .charge c ∘ k) x

  bind-charge : ∀ {c e k} → bind {A = A} (F X .charge c e) k ≡ A .charge c (bind {A = A} e k)
  bind-charge {A = A} {e = e} =
    rec-unique
      (A .is-preorder)
      (λ z → bind {A = A} (_ , z) _)
      (λ z → A .charge _ (bind {A = A} (_ , z) _))
      (λ _ → A .charge-+)
      (e .snd)

  bind-β : ∀ {x k} → bind {A = A} (ret {X} x) k ≡ k x
  bind-β {A = A} = A .charge-0

  bind-chargeℕ : ∀ n {e k} → bind {A = A} (chargeℕ (F X) n e) k ≡ chargeℕ A n (bind {A = A} e k)
  bind-chargeℕ zero = refl
  bind-chargeℕ {A = A} (suc n) {e} {k} =
    bind-charge {A = A} {c = 1ℂ} {e = chargeℕ (F _) n e} {k = k} ∙ cong (A .charge 1ℂ) (bind-chargeℕ n {e} {k})

  bind-chargeℕ-ret : ∀ n {x k} → bind {A = A} (chargeℕ (F X) n (ret x)) k ≡ chargeℕ A n (k x)
  bind-chargeℕ-ret {A = A} n {x} {k} =
    bind-chargeℕ n {ret x} {k} ∙ cong (chargeℕ A n) (bind-β {A = A} {x = x} {k = k})

  syntax bind {A = A} e (λ x → k) = bind[ A ] x ← e ⨾ k

  variable
    Δ : 𝒞

  F-rec : (X → U A) → (F X ⊸ A)
  F-rec {A = A} k .U (c , x) = rec (A .is-preorder) (A .charge c ∘ k) x
  F-rec {A = A} _ .charge _ (c , x) =
    rec-unique
      (A .is-preorder)
      (λ z → bind {A = A} (_ , z) _)
      (λ z → A .charge _ (bind {A = A} (_ , z) _))
      (λ _ → A .charge-+)
      x

  F-rec-β : {x : X} {k : X → U A} → F-rec {A = A} k .U (ret {X} x) ≡ k x
  F-rec-β {A = A} = A .charge-0

  F-rec-η : F-rec (ret {X}) ≡ idᶜ
  F-rec-η =
    ⊸-path refl refl (funExt λ (c , x) →
      rec-unique
        (F _ .is-preorder)
        (λ z → F-rec {A = F _} ret .U (c , z))
        (λ z → c , z)
        (λ x → cong (_, ηᴾ x) (+ℂ-identityʳ c))
        x)

  F-rec-assoc :
      (h : X → U (F Y))
    → (k : Y → U A)
    → (e : U (F X))
    → F-rec {A = A} k .U (F-rec {A = F Y} h .U e)
      ≡ F-rec {A = A} (λ x → F-rec {A = A} k .U (h x)) .U e
  F-rec-assoc {Y = Y} {A = A} h k (c , x) =
    rec-unique
      (A .is-preorder)
      (λ z → F-rec {A = A} k .U (F-rec {A = F Y} h .U (c , z)))
      (λ z → F-rec {A = A} (λ x → F-rec {A = A} k .U (h x)) .U (c , z))
      (λ x → F-rec {A = A} k .charge c (h x))
      x

  F-rec-charge :
      (h : X → U A)
    → (c : ℂ)
    → (e : U (F X))
    → F-rec {A = A} (λ x → A .charge c (h x)) .U e
      ≡ F-rec {A = A} h .U (F X .charge c e)
  F-rec-charge {A = A} h c (c' , x) =
    cong (λ e → rec (A .is-preorder) e x) $
    funExt λ x →
    sym (A .charge-+) ∙ cong (λ d → A .charge d (h x)) (+ℂ-comm c' c)

  F-rec-map :
      (f : A ⊸ B)
    → (h : X → U A)
    → (e : U (F X))
    → f .U (F-rec {A = A} h .U e)
      ≡ F-rec {A = B} (λ x → f .U (h x)) .U e
  F-rec-map {A = A} {B = B} f h (c , x) =
    rec-unique
      (B .is-preorder)
      (λ z → f .U (F-rec {A = A} h .U (c , z)))
      (λ z → F-rec {A = B} (λ x → f .U (h x)) .U (c , z))
      (λ x → f .charge c (h x))
      x

private
  F-rec-isEquiv : isEquiv (F-rec {X} {A})
  F-rec-isEquiv {X} {A} = isoToIsEquiv $
    iso
      (F-rec {X} {A})
      (λ f → f .U ∘ ret {X})
      (λ f → ⊸-path refl refl (funExt λ e → sym (F-rec-map f ret e) ∙ cong (f .U) (cong ((_$ e) ∘ U) F-rec-η)))
      (λ g → funExt λ x → F-rec-β)

F-adjoint : (X → U A) ≃ (F X ⊸ A)
F-adjoint = F-rec , F-rec-isEquiv

map : (X → Y) → (F X ⊸ F Y)
map f = F-rec (ret ∘ f)

F-rec-path : (f g : F X ⊸ A) →
  (f .U ∘ ret ≡ g .U ∘ ret)
  → f ≡ g
F-rec-path f g pf-ret = sym (secEq F-adjoint f) ∙ cong F-rec pf-ret ∙ secEq F-adjoint g

costed : (X → Y) → (X → ℂ) → (F X ⊸ F Y)
costed f Φ = F-rec λ x → F _ .charge (Φ x) (ret (f x))

costed-cong : {f g : X → Y} {Φ Ψ : X → ℂ}
  → (∀ x → f x ≡ g x) → (∀ x → Φ x ≡ Ψ x) → costed f Φ ≡ costed g Ψ
costed-cong p q i = costed (λ x → p x i) (λ x → q x i)

costed-⨾ᶜ : (f : X → Y) (Φ : X → ℂ) (g : Y → Z) (Ψ : Y → ℂ)
  → costed f Φ ⨾ᶜ costed g Ψ ≡ costed (g ∘ f) (λ x → Φ x +ℂ Ψ (f x))
costed-⨾ᶜ f Φ g Ψ =
  F-rec-path _ _ (funExt λ x →
      cong (costed g Ψ .U) F-rec-β
    ∙ costed g Ψ .charge (Φ x) (ret (f x))
    ∙ cong (F _ .charge (Φ x)) F-rec-β
    ∙ sym (F _ .charge-+)
    ∙ sym F-rec-β)

costed-map : (f : X → Y) (g : Y → Z) (Ψ : Y → ℂ)
  → map f ⨾ᶜ costed g Ψ ≡ costed (g ∘ f) (Ψ ∘ f)
costed-map f g Ψ =
  F-rec-path _ _ (funExt λ x → cong (costed g Ψ .U) F-rec-β ∙ F-rec-β ∙ sym F-rec-β)
