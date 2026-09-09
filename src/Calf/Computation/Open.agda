module Calf.Computation.Open where

open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Power
open import Calf.Computation.Pullback

open import Calf.Value.Open as ◯ public
  hiding (map; map-∘; join; bind)

◯ᶜ : 𝒞 → 𝒞
◯ᶜ = ⟨ ABS ⟩ ⇀_

η◦ᶜ : A ⊸ ◯ᶜ A
η◦ᶜ .U = η◦
η◦ᶜ .charge _ _ = refl

isModalᶜ : 𝒞 → 𝒱
isModalᶜ A = isModal (U A)

𝒞◦ : 𝒱₁
𝒞◦ = 𝒞WithStr isModalᶜ

𝒞◦-path : {A◦ B◦ : 𝒞◦} → ⟨ A◦ ⟩ᶜ ≡ ⟨ B◦ ⟩ᶜ → A◦ ≡ B◦
𝒞◦-path p = Σ≡Prop (λ A → isPropIsEquiv (η◦ᶜ {A} .U)) p

isModalᶜ◯ᶜ : isModalᶜ (◯ᶜ A)
isModalᶜ◯ᶜ = isModal◯

◯ᶜ◦ : 𝒞 → 𝒞◦
◯ᶜ◦ A = ◯ᶜ A , isModalᶜ◯ᶜ {A}

U◦ : 𝒞◦ → 𝒱◦
U◦ A◦ = U ⟨ A◦ ⟩ᶜ , strᶜ A◦

map : (A ⊸ B) → (◯ᶜ A ⊸ ◯ᶜ B)
map f .U = ◯.map (f .U)
map f .charge c a◦ = funExt λ abs → f .charge c (a◦ abs)

map-∘ : (f : A ⊸ B) (g : B ⊸ C) → map f ⨾ᶜ map g ≡ map (f ⨾ᶜ g)
map-∘ f g = ⊸-path refl refl (funExt (◯.map-∘ (f .U) (g .U)))

join : ◯ᶜ (◯ᶜ A) ⊸ ◯ᶜ A
join .U = ◯.join
join .charge c a◦ = refl

bind : (A ⊸ ◯ᶜ B) → (◯ᶜ A ⊸ ◯ᶜ B)
bind {B = B} k = map k ⨾ᶜ join {B}

◯ᶜ-rec : (B◦ : 𝒞◦) → (A ⊸ ⟨ B◦ ⟩ᶜ) → (◯ᶜ A ⊸ ⟨ B◦ ⟩ᶜ)
◯ᶜ-rec B◦ g .U = ◯.elim (λ _ → strᶜ B◦) (g .U)
◯ᶜ-rec {A = A} B◦ g .charge c =
  ◯.elim (λ a◦ → ◯.isModal≡ (strᶜ B◦)) λ a →
      ◯.elim-β (λ _ → strᶜ B◦) (g .U) (A .charge c a)
    ∙ g .charge c a
    ∙ cong (⟨ B◦ ⟩ᶜ .charge c) (sym (◯.elim-β (λ _ → strᶜ B◦) (g .U) a))

opaque
  ⊸-precomp-η◦ᶜ-isEquiv : {A : 𝒞} (B◦ : 𝒞◦)
    → isEquiv (λ (f : ◯ᶜ A ⊸ ⟨ B◦ ⟩ᶜ) → η◦ᶜ {A} ⨾ᶜ f)
  ⊸-precomp-η◦ᶜ-isEquiv B◦ =
    isoToIsEquiv (iso (η◦ᶜ ⨾ᶜ_) (◯ᶜ-rec B◦)
      (λ g → ⊸-path refl refl (funExt (◯.elim-β (λ _ → strᶜ B◦) (g .U))))
      (λ f → ⊸-path refl refl (sym (◯.◯-rec-unique (strᶜ B◦) refl))))

⊸-precomp-η◦ᶜ-≃ : {A : 𝒞} (B◦ : 𝒞◦) → (◯ᶜ A ⊸ ⟨ B◦ ⟩ᶜ) ≃ (A ⊸ ⟨ B◦ ⟩ᶜ)
⊸-precomp-η◦ᶜ-≃ B◦ = (η◦ᶜ ⨾ᶜ_) , ⊸-precomp-η◦ᶜ-isEquiv B◦

Pullback-◯ᶜ : ∀ {A B C} (f : A ⊸ C) (g : B ⊸ C) → ◯ᶜ (Pullback f g) ≡ Pullback (map f) (map g)
Pullback-◯ᶜ {A} {B} {C} f g = conservativity fwd fwd-equiv
  where
    fwd : ◯ᶜ (Pullback f g) ⊸ Pullback (map f) (map g)
    fwd .U e =
      ((λ abs → e abs .fst .fst) , (λ abs → e abs .fst .snd)) ,
      funExt (λ abs → e abs .snd)
    fwd .charge c e =
      ΣPathP (refl , isProp→PathP (λ i → is-set (◯ᶜ C) _ _) _ _)

    inv : U (Pullback (map f) (map g)) → U (◯ᶜ (Pullback f g))
    inv ((a◦ , b◦) , p) abs = (a◦ abs , b◦ abs) , funExt⁻ p abs

    fwd-equiv : isEquivᶜ fwd
    fwd-equiv = isoToIsEquiv (iso (fwd .U) inv (λ _ → refl) (λ _ → refl))

◯ᶜ-eval-open : ⟨ ABS ⟩ → (A : 𝒞) → ◯ᶜ A ⊸ A
◯ᶜ-eval-open abs A .U a◦ = a◦ abs
◯ᶜ-eval-open abs A .charge c a◦ = refl

◯ᶜ-eval-open-isEquiv
  : (abs : ⟨ ABS ⟩) (A : 𝒞)
  → isEquivᶜ (◯ᶜ-eval-open abs A)
◯ᶜ-eval-open-isEquiv abs A =
  isoToIsEquiv
    (iso
      (◯ᶜ-eval-open abs A .U)
      η◦
      (λ _ → refl)
      (λ a◦ → funExt λ abs' → cong a◦ (str ABS abs abs')))

◯ᶜ-open-≃ : ⟨ ABS ⟩ → ◯ᶜ A ≃ᶜ A
◯ᶜ-open-≃ {A} abs = ◯ᶜ-eval-open abs A , ◯ᶜ-eval-open-isEquiv abs A

◯ᶜ-open : ⟨ ABS ⟩ → ◯ᶜ A ≡ A
◯ᶜ-open abs = uaᶜ (◯ᶜ-open-≃ abs)

◯ᶜ-map-openP : ∀ (abs : ⟨ ABS ⟩) (f : A ⊸ B)
  → PathP (λ i → ◯ᶜ-open {A} abs i ⊸ ◯ᶜ-open {B} abs i)
      (map f)
      f
◯ᶜ-map-openP {A} {B} abs f =
  ⊸-path
    (◯ᶜ-open {A} abs)
    (◯ᶜ-open {B} abs)
    (ua→
      {e = ◯ᶜ-eval-open abs A .U , ◯ᶜ-eval-open-isEquiv abs A}
      {B = λ i → U (◯ᶜ-open {B} abs i)}
      (λ a◦ →
        ua-gluePath
          (◯ᶜ-eval-open abs B .U , ◯ᶜ-eval-open-isEquiv abs B)
          refl))

◯ᶜ-point-openP : ∀ (abs : ⟨ ABS ⟩) (a◦ : U (◯ᶜ A)) (a : U A)
  → a◦ abs ≡ a
  → PathP (λ i → U (◯ᶜ-open {A} abs i)) a◦ a
◯ᶜ-point-openP {A} abs a◦ a p =
  ua-gluePath
    (◯ᶜ-eval-open abs A .U , ◯ᶜ-eval-open-isEquiv abs A)
    p

private
  embed : ∀ {X A} → Σᶜ₌ X A .U → Σᶜ₌ X (◯ᶜ ∘ A) .U
  embed (x , a) = x , η◦ a

Σᶜ-◯ᶜ-fwd : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → ◯ᶜ (Σᶜ₌ X A) ⊸ ◯ᶜ (Σᶜ₌ X (◯ᶜ ∘ A))
Σᶜ-◯ᶜ-fwd X A = map (Σᶜ-map {A = A} {B = ◯ᶜ ∘ A} (λ _ → η◦ᶜ))

Σᶜ-◯ᶜ-fwd-equiv : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → isEquivᶜ (Σᶜ-◯ᶜ-fwd X A)
Σᶜ-◯ᶜ-fwd-equiv X A =
  subst isEquiv (funExt⁻ ◯.map′≡map (embed {X} {A})) (invEquiv ○Σ○≃○Σ .snd)

Σᶜ-◯ᶜ : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → ◯ᶜ (Σᶜ₌ X A) ≡ ◯ᶜ (Σᶜ₌ X (◯ᶜ ∘ A))
Σᶜ-◯ᶜ X A =
  conservativity (Σᶜ-◯ᶜ-fwd X A) (Σᶜ-◯ᶜ-fwd-equiv X A)
