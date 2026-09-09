module Calf.Computation.Closed where

open import Cubical.Foundations.Path
  using (compPathlEquiv; compPathrEquiv)

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value
open import Calf.Computation
open import Calf.Computation.Copower
open import Calf.Computation.Pullback

open import Calf.Value.Closed as ● public
  hiding (map; map-∘; join; bind)

●ᶜ : 𝒞 → 𝒞
●ᶜ A .U = ● (A .U)
●ᶜ A .is-preorder = isPreorder● (A .is-preorder)
●ᶜ A .charge = ●.map ∘ A .charge
●ᶜ A .charge-0 {a•} = lemma
  where
    opaque
      lemma : ●ᶜ A .charge 0ℂ a• ≡ a•
      lemma =
        ●.elim (λ a• → ●-≡-isModal (●ᶜ A .charge 0ℂ a•) a•)
          (λ a → cong η• (A .charge-0 {a}))
          a•
●ᶜ A .charge-+ {a•} {c₁} {c₂} = lemma
  where
    opaque
      lemma : ●ᶜ A .charge (c₁ +ℂ c₂) a• ≡ ●ᶜ A .charge c₁ (●ᶜ A .charge c₂ a•)
      lemma =
        ●.elim (λ a• → ●-≡-isModal (●ᶜ A .charge (c₁ +ℂ c₂) a•) (●ᶜ A .charge c₁ (●ᶜ A .charge c₂ a•)))
          (λ a → cong η• (A .charge-+ {a} {c₁} {c₂}))
          a•

η•ᶜ : A ⊸ ●ᶜ A
η•ᶜ .U = η•
η•ᶜ .charge _ _ = refl

isModalᶜ : 𝒞 → 𝒱
isModalᶜ A = isModal (U A)

𝒞• : 𝒱₁
𝒞• = 𝒞WithStr isModalᶜ

𝒞•-path : {A• B• : 𝒞•} → ⟨ A• ⟩ᶜ ≡ ⟨ B• ⟩ᶜ → A• ≡ B•
𝒞•-path p = Σ≡Prop (λ A → isPropIsEquiv (η•ᶜ {A} .U)) p

isModalᶜ●ᶜ : isModalᶜ (●ᶜ A)
isModalᶜ●ᶜ = isModal●

●ᶜ• : 𝒞 → 𝒞•
●ᶜ• A = ●ᶜ A , isModalᶜ●ᶜ {A}

U• : 𝒞• → 𝒱•
U• A• .fst = ⟨ A• ⟩ᶜ .U
U• A• .snd = A• .snd

opaque
  map-charge : (f : A ⊸ B) (c : ℂ) (a• : U (●ᶜ A))
    → ●.map (f .U) (●ᶜ A .charge c a•) ≡ ●ᶜ B .charge c (●.map (f .U) a•)
  map-charge f c =
    ●.elim (λ _ → ●-≡-isModal _ _) (λ a → cong η• (f .charge c a))

map : (A ⊸ B) → (●ᶜ A ⊸ ●ᶜ B)
map f .U = ●.map (f .U)
map f .charge = map-charge f

map-∘ : (f : A ⊸ B) (g : B ⊸ C) → map f ⨾ᶜ map g ≡ map (f ⨾ᶜ g)
map-∘ f g = ⊸-path refl refl (funExt (●.map-∘ (f .U) (g .U)))

opaque
  map-id : map (idᶜ {A}) ≡ idᶜ
  map-id {A} =
    ⊸-path refl refl
      (funExt (●.ind-prop _ (λ _ → ●.isSet● (is-set A) _ _) (λ _ → refl) (λ _ → refl)))

opaque
  map-id-equiv : isEquiv (map (idᶜ {A}) .U)
  map-id-equiv {A} = subst isEquiv (cong (λ h → h .U) (sym (map-id {A}))) (idIsEquiv _)

opaque
  map-open : ⟨ ABS ⟩ → (f g : A ⊸ B) → map f ≡ map g
  map-open {A} {B} p f g =
    ⊸-path
      {A₀ = ●ᶜ A}
      {A₁ = ●ᶜ A}
      {B₀ = ●ᶜ B}
      {B₁ = ●ᶜ B}
      refl
      refl
      (funExt λ a• →
        ◯-isProp● p
          (map {A = A} {B = B} f .U a•)
          (map {A = A} {B = B} g .U a•))

opaque
  join-charge : (c : ℂ) (a•• : U (●ᶜ (●ᶜ A)))
    → ●.join (●ᶜ (●ᶜ A) .charge c a••) ≡ ●ᶜ A .charge c (●.join a••)
  join-charge c =
    ●.elim (λ _ → ●-≡-isModal _ _) (λ _ → refl)

join : ●ᶜ (●ᶜ A) ⊸ ●ᶜ A
join .U = ●.join
join {A} .charge = join-charge {A}

bind : (A ⊸ ●ᶜ B) → (●ᶜ A ⊸ ●ᶜ B)
bind k = map k ⨾ᶜ join

opaque
  bind-map : (k : A ⊸ ●ᶜ B) (f : B ⊸ C) → bind k ⨾ᶜ map f ≡ bind (k ⨾ᶜ map f)
  bind-map k f =
    ⊸-path refl refl
      (funExt (●.elim (λ _ → ●-≡-isModal _ _) (λ _ → refl)))

opaque
  bind-η• : (f : A ⊸ B) → bind (f ⨾ᶜ η•ᶜ) ≡ map f
  bind-η• f =
    ⊸-path refl refl
      (funExt (●.elim (λ _ → ●-≡-isModal _ _) (λ _ → refl)))

opaque
  ●ᶜ-rec-charge : (B• : 𝒞•) (g : A ⊸ ⟨ B• ⟩ᶜ) (c : ℂ) (a• : U (●ᶜ A))
    → ●.elim (λ _ → strᶜ B•) (g .U) (●ᶜ A .charge c a•)
    ≡ ⟨ B• ⟩ᶜ .charge c (●.elim (λ _ → strᶜ B•) (g .U) a•)
  ●ᶜ-rec-charge B• g c = ●.elim (λ a• → ●.isModal≡ (strᶜ B•)) (g .charge c)

●ᶜ-rec : (B• : 𝒞•) → (A ⊸ ⟨ B• ⟩ᶜ) → (●ᶜ A ⊸ ⟨ B• ⟩ᶜ)
●ᶜ-rec B• g .U = ●.elim (λ _ → strᶜ B•) (g .U)
●ᶜ-rec B• g .charge = ●ᶜ-rec-charge B• g

●ᶜ-rec-β : (B• : 𝒞•) (g : A ⊸ ⟨ B• ⟩ᶜ) (a : U A)
  → ●ᶜ-rec B• g .U (η• a) ≡ g .U a
●ᶜ-rec-β B• g a = refl

opaque
  ⊸-precomp-η•ᶜ-isEquiv : {A : 𝒞} (B• : 𝒞•)
    → isEquiv (λ (f : ●ᶜ A ⊸ ⟨ B• ⟩ᶜ) → η•ᶜ ⨾ᶜ f)
  ⊸-precomp-η•ᶜ-isEquiv B• =
    isoToIsEquiv (iso (η•ᶜ ⨾ᶜ_) (●ᶜ-rec B•)
      (λ g → ⊸-path refl refl refl)
      (λ f → ⊸-path refl refl
        (funExt (●.elim (λ a• → ●.isModal≡ (strᶜ B•)) (λ a → refl)))))

⊸-precomp-η•ᶜ-≃ : {A : 𝒞} (B• : 𝒞•) → (●ᶜ A ⊸ ⟨ B• ⟩ᶜ) ≃ (A ⊸ ⟨ B• ⟩ᶜ)
⊸-precomp-η•ᶜ-≃ B• = (η•ᶜ ⨾ᶜ_) , ⊸-precomp-η•ᶜ-isEquiv B•

●ᶜ-map-chargeᶜ
  : (c : ℂ) (a• : U (●ᶜ A))
  → map (chargeᶜ {A = A} c) .U a• ≡ ●ᶜ A .charge c a•
●ᶜ-map-chargeᶜ c =
  ●.elim (λ _ → ●-≡-isModal _ _) (λ _ → refl)

module _ {A B C : 𝒞} where

  Pullback-●ᶜ : (f : A ⊸ C) (g : B ⊸ C) → ●ᶜ (Pullback f g) ≡ Pullback (map f) (map g)
  Pullback-●ᶜ f g = conservativity fwd (equivIsEquiv e)
    where
      e : U (●ᶜ (Pullback f g)) ≃ U (Pullback (map f) (map g))
      e = ●.●-pullback

      isProp-at : ⟨ ABS ⟩ → isProp (U (Pullback (map f) (map g)))
      isProp-at abs =
        isPropΣ (isProp× (◯-isProp● abs) (◯-isProp● abs)) λ _ →
        isProp→isSet (◯-isProp● abs) _ _

      fwd-charge : (c : ℂ) (a• : U (●ᶜ (Pullback f g)))
        → equivFun e (●ᶜ (Pullback f g) .charge c a•)
        ≡ Pullback (map f) (map g) .charge c (equivFun e a•)
      fwd-charge c =
        ind-prop _ (λ _ → is-set (Pullback (map f) (map g)) _ _)
          (λ t → ΣPathP
            ( ΣPathP
              ( ●.●-pullback-β₁ (Pullback f g .charge c t)
                ∙ sym (cong (●ᶜ A .charge c) (●.●-pullback-β₁ t))
              , ●.●-pullback-β₂ (Pullback f g .charge c t)
                ∙ sym (cong (●ᶜ B .charge c) (●.●-pullback-β₂ t)) )
            , isProp→PathP (λ i → is-set (●ᶜ C) _ _) _ _))
          (λ abs → isProp-at abs _ _)

      fwd : ●ᶜ (Pullback f g) ⊸ Pullback (map f) (map g)
      fwd .U = equivFun e
      fwd .charge = fwd-charge

private
  embed : ∀ {X A} → Σᶜ₌ X A .U → Σᶜ₌ X (●ᶜ ∘ A) .U
  embed (x , a) = x , η• a

Σᶜ-●ᶜ-fwd : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → ●ᶜ (Σᶜ₌ X A) ⊸ ●ᶜ (Σᶜ₌ X (●ᶜ ∘ A))
Σᶜ-●ᶜ-fwd X A = map (Σᶜ-map (λ _ → η•ᶜ))

Σᶜ-●ᶜ-fwd-equiv : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → isEquivᶜ (Σᶜ-●ᶜ-fwd X A)
Σᶜ-●ᶜ-fwd-equiv X A =
  subst isEquiv (funExt⁻ ●.map′≡map (embed {X} {A})) (invEquiv ●Σ●≃●Σ .snd)

Σᶜ-●ᶜ : (X : 𝒱₌) (A : ⟨ X ⟩ → 𝒞) → ●ᶜ (Σᶜ₌ X A) ≡ ●ᶜ (Σᶜ₌ X (●ᶜ ∘ A))
Σᶜ-●ᶜ X A =
  conservativity (Σᶜ-●ᶜ-fwd X A) (Σᶜ-●ᶜ-fwd-equiv X A)
