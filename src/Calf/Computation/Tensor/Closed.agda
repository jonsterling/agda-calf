module Calf.Computation.Tensor.Closed where

open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[equivFunA≃B∘f]→isEquiv[f])

open import Calf.Core.Abstract
open import Calf.Value
import Calf.Value.Closed as ●
import Calf.Value.Open as ◯
open import Calf.Computation
open import Calf.Computation.Closed as ●ᶜ hiding (map)

open import Calf.Computation.Tensor.Base

module _ {A B : 𝒞} where
  private
    ⊗•-isContr : (abs : ⟨ ABS ⟩) → isContr (U (●ᶜ A ⊗ ●ᶜ B))
    ⊗•-isContr abs = ⊗-isContr (◯-isConnected abs) (◯-isConnected abs)

  private
    ⊗• : 𝒞•
    ⊗• = (●ᶜ A ⊗ ●ᶜ B) , isConnected◯→isModal● (◯.◯isContr→isConnected ⊗•-isContr)

  ●ᶜ-⊗-fwd : ●ᶜ (A ⊗ B) ⊸ (●ᶜ A ⊗ ●ᶜ B)
  ●ᶜ-⊗-fwd = ●ᶜ-rec ⊗• (map₂ η•ᶜ η•ᶜ)

  private
    comb : U (●ᶜ A) → U (●ᶜ B) → U (●ᶜ (A ⊗ B))
    comb a• b• = ●.elim (λ _ → ●.isModal●) (λ a → ●.map (a ∥_) b•) a•

    comb-chargeˡ : ∀ c a• b• → comb (●ᶜ A .charge c a•) b• ≡ ●ᶜ (A ⊗ B) .charge c (comb a• b•)
    comb-chargeˡ c =
      ●.elim (λ _ → ●.isModalΠ λ _ → ●.●-≡-isModal _ _) λ a →
        ●.elim (λ _ → ●.●-≡-isModal _ _) λ b → refl

    comb-chargeʳ : ∀ c a• b• → comb a• (●ᶜ B .charge c b•) ≡ ●ᶜ (A ⊗ B) .charge c (comb a• b•)
    comb-chargeʳ c =
      ●.elim (λ _ → ●.isModalΠ λ _ → ●.●-≡-isModal _ _) λ a →
        ●.elim (λ _ → ●.●-≡-isModal _ _) λ b → cong ●.η• (sym (∥-slide c a b))

    sect-pt : ∀ a• b• → ●ᶜ-⊗-fwd .U (comb a• b•) ≡ ηᴾ (inj a• b•)
    sect-pt a• b• =
      ●.ind-prop (λ a• → ●ᶜ-⊗-fwd .U (comb a• b•) ≡ ηᴾ (inj a• b•))
        (λ _ → isPreorder→isSet isPreorderᴾ _ _)
        (λ a →
          ●.ind-prop (λ b• → ●ᶜ-⊗-fwd .U (comb (●.η• a) b•) ≡ ηᴾ (inj (●.η• a) b•))
            (λ _ → isPreorder→isSet isPreorderᴾ _ _)
            (λ b → ●ᶜ-rec-β ⊗• (map₂ η•ᶜ η•ᶜ) (ηᴾ (inj a b)))
            (λ abs → isContr→isProp (⊗•-isContr abs) _ _)
            b•)
        (λ abs → isContr→isProp (⊗•-isContr abs) _ _)
        a•

  ⊗-str● : (●ᶜ A ⊗ ●ᶜ B) ⊸ ●ᶜ (A ⊗ B)
  ⊗-str● = ⊗-rec comb comb-chargeˡ comb-chargeʳ

  ●ᶜ-⊗-equiv : isEquivᶜ ●ᶜ-⊗-fwd
  ●ᶜ-⊗-equiv = isoToIsEquiv (iso (●ᶜ-⊗-fwd .U) (⊗-str● .U) sect retr)
    where
      sect : ∀ y → ●ᶜ-⊗-fwd .U (⊗-str● .U y) ≡ y
      sect = ⊗₀-rec-unique isPreorderᴾ (λ y → ●ᶜ-⊗-fwd .U (⊗-str● .U y)) (λ y → y) sect-pt

      retr : ∀ x → ⊗-str● .U (●ᶜ-⊗-fwd .U x) ≡ x
      retr =
        ●.ind-prop _ (λ _ → ●.isSet● (isPreorder→isSet isPreorderᴾ) _ _)
          (⊗₀-rec-unique (●.isPreorder● isPreorderᴾ) (λ w → ⊗-str● .U (●ᶜ-⊗-fwd .U (●.η• w))) ●.η•
            (λ a b → cong (⊗-str● .U) (●ᶜ-rec-β ⊗• (map₂ η•ᶜ η•ᶜ) (ηᴾ (inj a b)))))
          (λ abs → ●.◯-isProp● abs _ _)

  ●ᶜ-⊗ : ●ᶜ (A ⊗ B) ≡ (●ᶜ A ⊗ ●ᶜ B)
  ●ᶜ-⊗ = conservativity ●ᶜ-⊗-fwd ●ᶜ-⊗-equiv

●ᶜ-⊗-natural : {A A' B B' : 𝒞} (f : A ⊸ A') (g : B ⊸ B')
  → ∀ w →
    map₂ (●ᶜ.map f) (●ᶜ.map g) .U (●ᶜ-⊗-fwd .U w)
    ≡ ●ᶜ-⊗-fwd .U (●ᶜ.map (map₂ f g) .U w)
●ᶜ-⊗-natural {A} {A'} {B} {B'} f g =
  ●.ind-prop _ (λ _ → isPreorder→isSet isPreorderᴾ _ _)
    (⊗₀-rec-unique isPreorderᴾ
      (λ z → map₂ (●ᶜ.map f) (●ᶜ.map g) .U (●ᶜ-⊗-fwd .U (●.η• z)))
      (λ z → ●ᶜ-⊗-fwd .U (●ᶜ.map (map₂ f g) .U (●.η• z)))
      (λ a b → refl))
    (λ abs → isContr→isProp (⊗-isContr (◯-isConnected abs) (◯-isConnected abs)) _ _)

opaque
  ●ᶜ-map₂-equiv : {A A' B B' : 𝒞} {f : A ⊸ A'} {g : B ⊸ B'}
    → isEquiv (●ᶜ.map f .U) → isEquiv (●ᶜ.map g .U)
    → isEquiv (●ᶜ.map (map₂ f g) .U)
  ●ᶜ-map₂-equiv {A} {A'} {B} {B'} {f} {g} fe ge =
    isEquiv[equivFunA≃B∘f]→isEquiv[f] (●ᶜ.map (map₂ f g) .U) (●ᶜ-⊗-fwd .U , ●ᶜ-⊗-equiv)
      (subst isEquiv (funExt (●ᶜ-⊗-natural f g))
        (compEquiv (●ᶜ-⊗-fwd .U , ●ᶜ-⊗-equiv)
          (map₂ (●ᶜ.map f) (●ᶜ.map g) .U , map₂-equivᶜ {f = ●ᶜ.map f} {g = ●ᶜ.map g} fe ge) .snd))
