module Calf.Computation.Tensor.Free where

open import Cubical.Foundations.Univalence using (ua→; ua-gluePath)

open import Calf.Core.Cost
open import Calf.Value
open import Calf.Value.Unit
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Empty
open import Calf.Computation.Free

open import Calf.Computation.Tensor.Base

opaque
  unfolding F

  F-monoidal : F X ⊗ F Y ≡ F (X × Y)
  F-monoidal {X} {Y} = sym (conservativity bwd bwd-equiv)
    where
      bwd : F (X × Y) ⊸ F X ⊗ F Y
      bwd = F-rec (λ (x , y) → ret x ∥ ret y)

      fwd : U (F X ⊗ F Y) → U (F (X × Y))
      fwd = rec (F (X × Y) .is-preorder) λ
        { (inj (c₁ , x) (c₂ , y)) → (c₁ +ℂ c₂) , map2ᴾ _,_ x y
        ; (slide c (c₁ , x) (c₂ , y) i) →
            cong (_, map2ᴾ _,_ x y)
              ( cong (_+ℂ c₂) (+ℂ-comm c c₁) ∙ +ℂ-assoc c₁ c c₂ ) i
        }

      charge-ret : (c : ℂ) (z : Z) → F Z .charge c (ret z) ≡ (c , ηᴾ z)
      charge-ret c z = cong (_, ηᴾ z) (+ℂ-identityʳ c)

      bwd-sect : ∀ v → bwd .U (fwd v) ≡ v
      bwd-sect =
        ⊗₀-rec-unique isPreorderᴾ (λ v → bwd .U (fwd v)) (λ v → v)
          (λ (c₁ , x) (c₂ , y) →
            rec-unique2 isPreorderᴾ
              (λ x y → bwd .U ((c₁ +ℂ c₂) , map2ᴾ _,_ x y))
              (λ x y → ηᴾ (inj (c₁ , x) (c₂ , y)))
              (λ x y →
                  (F X ⊗ F Y) .charge-+ {ret x ∥ ret y} {c₁} {c₂}
                ∙ cong ((F X ⊗ F Y) .charge c₁) (∥-slide {A = F X} {B = F Y} c₂ (ret x) (ret y))
                ∙ cong₂ _∥_ (charge-ret c₁ x) (charge-ret c₂ y))
              x y)

      bwd-retr : ∀ u → fwd (bwd .U u) ≡ u
      bwd-retr (c , w) =
        rec-unique (F (X × Y) .is-preorder)
          (λ w → fwd (bwd .U (c , w)))
          (c ,_)
          (λ (x , y) →
            cong (_, ηᴾ (x , y)) (cong (_+ℂ 0ℂ) (+ℂ-identityʳ c) ∙ +ℂ-identityʳ c))
          w

      bwd-equiv : isEquivᶜ bwd
      bwd-equiv = isoToIsEquiv (iso (bwd .U) fwd bwd-sect bwd-retr)

par : U (F X) → U (F Y) → U (F (X × Y))
par ex ey = transport (cong U F-monoidal) (ex ∥ ey)


module _ (X : 𝒱₌) where
  private
    Σᶜ-charge : (Φ : ⟨ X ⟩ → ℂ) → ([ x ∈ X ] ⋊ ⊤) ⊸ ([ x ∈ X ] ⋊ ⊤)
    Σᶜ-charge Φ = Σᶜ-map {A = const ⊤} {B = const ⊤} (λ x → chargeᶜ (Φ x))

  opaque
    unfolding F

    Σᶜ-F-fwd : ([ x ∈ X ] ⋊ ⊤) ⊸ F ⟨ X ⟩
    Σᶜ-F-fwd .U (x , c) = c , ηᴾ x
    Σᶜ-F-fwd .charge _ _ = refl

    F-Σᶜ-fwd : F ⟨ X ⟩ ⊸ ([ x ∈ X ] ⋊ ⊤)
    F-Σᶜ-fwd .U (c , x) =
      rec (Σᶜ₌ X (const ⊤) .is-preorder) (λ x → x , c) x
    F-Σᶜ-fwd .charge c (c' , x) =
      rec-unique
        (Σᶜ₌ X (const ⊤) .is-preorder)
        (λ x → F-Σᶜ-fwd .U (c +ℂ c' , x))
        (λ x → Σᶜ₌ X (const ⊤) .charge c (F-Σᶜ-fwd .U (c' , x)))
        (λ _ → refl)
        x

    F-Σᶜ-fwd-equiv : isEquivᶜ F-Σᶜ-fwd
    F-Σᶜ-fwd-equiv =
      isoToIsEquiv (iso (F-Σᶜ-fwd .U) (Σᶜ-F-fwd .U) sec retr)
      where
        sec : ∀ e → F-Σᶜ-fwd .U (Σᶜ-F-fwd .U e) ≡ e
        sec _ = refl

        retr : ∀ e → Σᶜ-F-fwd .U (F-Σᶜ-fwd .U e) ≡ e
        retr (c , x) =
          rec-unique
            (F ⟨ X ⟩ .is-preorder)
            (λ x → Σᶜ-F-fwd .U (F-Σᶜ-fwd .U (c , x)))
            (c ,_)
            (λ _ → refl)
            x

    F-Σᶜ : F ⟨ X ⟩ ≡ ([ x ∈ X ] ⋊ ⊤)
    F-Σᶜ = conservativity F-Σᶜ-fwd F-Σᶜ-fwd-equiv

    F-Σᶜ-potential : ∀ (Φ : ⟨ X ⟩ → ℂ)
      → PathP (λ i → F-Σᶜ i ⊸ F-Σᶜ i)
          (F-rec λ x → F _ .charge (Φ x) (ret x))
          (Σᶜ-charge Φ)
    F-Σᶜ-potential Φ =
      conservativity-⊸ F-Σᶜ-fwd F-Σᶜ-fwd-equiv F-Σᶜ-fwd F-Σᶜ-fwd-equiv
        (⊸-path refl refl (funExt naturality))
      where
        naturality : (e : U (F ⟨ X ⟩)) →
          F-Σᶜ-fwd .U (F-rec {A = F _} (λ x → F _ .charge (Φ x) (ret x)) .U e)
          ≡ Σᶜ-charge Φ .U (F-Σᶜ-fwd .U e)
        naturality (c , x) =
          rec-unique
            (Σᶜ₌ X (const ⊤) .is-preorder)
            (λ x →
              F-Σᶜ-fwd .U
                (F-rec {A = F _} (λ x → F _ .charge (Φ x) (ret x)) .U (c , x)))
            (λ x → Σᶜ-charge Φ .U (F-Σᶜ-fwd .U (c , x)))
            (λ x → cong (x ,_) (cong (c +ℂ_) (+ℂ-identityʳ _) ∙ +ℂ-comm c (Φ x)))
            x

opaque
  F-⊤ : F 1ᵛ ≡ ⊤
  F-⊤ = F-Σᶜ 1ᵛ₌ ∙ Σᶜ-1ᵛ

opaque
  F-0 : F 0ᵛ ≡ 0ᶜ
  F-0 = F-Σᶜ 0ᵛ₌ ∙ Σᶜ-0ᵛ
