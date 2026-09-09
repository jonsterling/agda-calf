module Calf.Value.Glue.Fracture where

open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath)
open import Cubical.Data.Sigma
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)

open import Calf.Core.Abstract
open import Calf.Value
open import Calf.Value.Closed as ●
open import Calf.Value.Open as ◯

open import Calf.Value.Glue.Base

module _ where
  open Fracture

  FractureGlue : 𝒱 → 𝒱
  FractureGlue = fromFracture ∘ toFracture

  fracture : X → FractureGlue X
  fracture x = (η• x , η◦ x) , refl

  fracture-modal : ●.isModalMap (fracture {X})
  fracture-modal {X} g =
    ●.isModal-≃ (invEquiv e) $
    ●.isModalΣ (isConnected◯→isModal● (◯.isConnectedMapη _)) λ _ →
    ●.isModalPathP $ ●.isModalΣ ●.isModal● λ _ → ●-≡-isModal _ _
    where
      e : _
      e =
        Σ-cong-equiv-snd (λ _ →
          congEquiv (Σ-cong-equiv-fst Σ-swap-≃ ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv ΣPath≃PathΣ)
        ∙ₑ invEquiv Σ-assoc-≃

  fracture-connected : ●.isConnectedMap (fracture {X})
  fracture-connected {X} g =
    ●.isConnected-≃ (invEquiv e) $
    ●.isConnectedΣ (●.isConnectedMapη _) λ _ →
    ●.isConnectedPathP isLex● $ ●.isConnectedMapη _
    where
      e : _
      e =
        Σ-cong-equiv-snd (λ _ →
          congEquiv
            (Σ-cong-equiv-snd (λ _ → isoToEquiv symIso) ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv ΣPath≃PathΣ)
        ∙ₑ invEquiv Σ-assoc-≃

  fracture-isEquiv : isEquiv (fracture {X})
  fracture-isEquiv = ●.isModal+isConnected→isEquiv fracture-modal fracture-connected

  -- This proof is a direct adaptation of https://agda.monade.li/ErasureOpen.html
  glue-fracture-retract : retract toFracture fromFracture
  glue-fracture-retract X = sym (ua (fracture , fracture-isEquiv))

  opaque
    proj•-connected-contract : (F : Fracture)
      → ●.isConnectedMap (λ (g : fromFracture F) → • g)
    proj•-connected-contract F x• =
      ●.isConnected-≃
        (invEquiv
          ( Σ-cong-equiv-fst
              (Σ-cong-equiv-snd (λ _ → isoToEquiv symIso) ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv (fiberProjEquiv _ _ x•)))
        (●.isConnectedMapη (F .χ• x•))

  proj•-connected : (F : Fracture) → ●.isConnectedMap (λ (g : fromFracture F) → • g)
  proj•-connected F x• .fst =
    ●.map (λ (x◦ , p) → ((x• , x◦) , sym p) , refl)
      (●.isConnectedMapη (F .χ• x•) .fst)
  proj•-connected F x• .snd =
    isContr→isProp (proj•-connected-contract F x•) _

  opaque
    proj◦-connected-contract : (F : Fracture)
      → ◯.isConnectedMap (λ (g : fromFracture F) → ◦ g)
    proj◦-connected-contract F x◦ =
      ◯.isConnected-≃
        (invEquiv
          ( Σ-cong-equiv-fst (Σ-cong-equiv-fst Σ-swap-≃ ∙ₑ Σ-assoc-≃)
          ∙ₑ invEquiv (fiberProjEquiv _ _ x◦)))
        (isModal●→isConnected◯
          (●.isModalΣ (F .X• .snd) λ x• → ●-≡-isModal _ _))

  proj◦-connected : (F : Fracture) → ◯.isConnectedMap (λ (g : fromFracture F) → ◦ g)
  proj◦-connected F x◦ .fst abs =
    ( (invIsEq (F .X• .snd) (∗ abs) , x◦)
    , ◯-isProp● abs (F .χ• (invIsEq (F .X• .snd) (∗ abs))) (η• x◦)
    ) , refl
  proj◦-connected F x◦ .snd =
    isContr→isProp (proj◦-connected-contract F x◦) _

  glue•-out : (F : Fracture) → ● (fromFracture F) → ⟨ F .X• ⟩
  glue•-out F = ●.elim (λ _ → F .X• .snd) (λ g → • g)

  glue•-in : (F : Fracture) → ⟨ F .X• ⟩ → ● (fromFracture F)
  glue•-in F = ●.reflection-inv (F .X• .snd) (proj•-connected F)

  glue•-equiv : (F : Fracture) → ● (fromFracture F) ≃ ⟨ F .X• ⟩
  glue•-equiv F =
    isoToEquiv
      (iso (glue•-out F) (glue•-in F)
        (●.reflection-sec (F .X• .snd) (proj•-connected F))
        (●.reflection-ret (F .X• .snd) (proj•-connected F)))

  glue◦-out : (F : Fracture) → ◯ (fromFracture F) → ⟨ F .X◦ ⟩
  glue◦-out F = ◯.elim (λ _ → F .X◦ .snd) (λ g → ◦ g)

  glue◦-in : (F : Fracture) → ⟨ F .X◦ ⟩ → ◯ (fromFracture F)
  glue◦-in F = ◯.reflection-inv (F .X◦ .snd) (proj◦-connected F)

  glue◦-equiv : (F : Fracture) → ◯ (fromFracture F) ≃ ⟨ F .X◦ ⟩
  glue◦-equiv F =
    isoToEquiv
      (iso (glue◦-out F) (glue◦-in F)
        (◯.reflection-sec (F .X◦ .snd) (proj◦-connected F))
        (◯.reflection-ret (F .X◦ .snd) (proj◦-connected F)))

  glue•-β : (F : Fracture) (g : fromFracture F)
    → equivFun (glue•-equiv F) (η• g) ≡ • g
  glue•-β F = ●.elim-β (λ _ → F .X• .snd) (λ g → • g)

  glue◦-β : (F : Fracture) (g : fromFracture F)
    → equivFun (glue◦-equiv F) (η◦ g) ≡ ◦ g
  glue◦-β F = ◯.elim-β (λ _ → F .X◦ .snd) (λ g → ◦ g)

  opaque
    square-χ•-path : {F G : Fracture}
      → (h : fromFracture F → fromFracture G)
      → (k : ⟨ F .X• ⟩ → ● ⟨ G .X◦ ⟩)
      → ((g : fromFracture F) → η• (◦ (h g)) ≡ k (• g))
      → PathP (λ i → ua (glue•-equiv F) i → ● (ua (glue◦-equiv G) i))
          (●.map (η◦ ∘ h))
          k
    square-χ•-path {F} {G} h k coh =
      ua→ (●.elim (λ _ → ●.isModalPathP ●.isModal●) λ g →
        congP (λ _ → η•) (ua-gluePath (glue◦-equiv G) (glue◦-β G (h g)))
        ▷ (coh g ∙ cong k (sym (glue•-β F g))))

  glue-fracture-χ•-path : (F : Fracture)
    → PathP (λ i → ua (glue•-equiv F) i → ● (ua (glue◦-equiv F) i))
        (●.map η◦)
        (F .χ•)
  glue-fracture-χ•-path F = square-χ•-path (λ g → g) (F .χ•) (λ g → sym (•→◦ g))

  glue-fracture-section : section toFracture fromFracture
  glue-fracture-section F =
    Fracture-path
      (𝒱•-path (●• (fromFracture F)) (F .X•) (ua (glue•-equiv F)))
      (𝒱◦-path (◯◦ (fromFracture F)) (F .X◦) (ua (glue◦-equiv F)))
      (glue-fracture-χ•-path F)

  fracture-and-gluing : 𝒱 ≃ Fracture
  fracture-and-gluing =
    isoToEquiv (iso toFracture fromFracture glue-fracture-section glue-fracture-retract)

  Glue-open-≃ : (F : Fracture) → ⟨ ABS ⟩ → fromFracture F ≃ ⟨ F .X◦ ⟩
  Glue-open-≃ F abs .fst g = ◦ g
  Glue-open-≃ F abs .snd .equiv-proof x◦ =
    ◯.isConnected→◯isContr (proj◦-connected F x◦) abs

module _ where
  toSquare : (X → Y) → Fracture-Square (toFracture X) (toFracture Y)
  toSquare f =
    (●.map f , ◯.map f) ,
    funExt (●.elim (λ x• → ●-≡-isModal _ _) (λ _ → refl))

  fracture-and-gluing-square : (X → Y) ≃ Fracture-Square (toFracture X) (toFracture Y)
  fracture-and-gluing-square {X} {Y} =
      (X → Y)
    ≃⟨ equivΠCod (λ _ → fracture , fracture-isEquiv) ⟩
      (X → FractureGlue Y)
    ≃⟨ isoToEquiv Σ-Π-Iso ⟩
      (Σ[ h ∈ (X → ● Y × ◯ Y) ] ((x : X) → ●.map η◦ (h x .fst) ≡ η• (h x .snd)))
    ≃⟨ Σ-cong-equiv-fst (isoToEquiv Σ-Π-Iso) ⟩
      (Σ[ (h• , h◦) ∈ (X → ● Y) × (X → ◯ Y) ]
        ((x : X) → ●.map η◦ (h• x) ≡ η• (h◦ x)))
    ≃⟨ Σ-cong-equiv-snd (λ _ → funExtEquiv) ⟩
      (Σ[ (h• , h◦) ∈ (X → ● Y) × (X → ◯ Y) ] (●.map η◦ ∘ h• ≡ η• ∘ h◦))
    ≃⟨ invEquiv (Σ-cong-equiv (≃-× precomp• precomp◦)
         (λ (f• , f◦) → congEquiv precomp•●◯)) ⟩
      Fracture-Square (toFracture X) (toFracture Y)
    ■
    where
      precomp◦ : (◯ X → ◯ Y) ≃ (X → ◯ Y)
      precomp◦ = ◯.precomp-η-≃ ◯.isModal◯

      precomp• : (● X → ● Y) ≃ (X → ● Y)
      precomp• = ●.precomp-η-≃ ●.isModal●

      precomp•●◯ : (● X → ● (◯ Y)) ≃ (X → ● (◯ Y))
      precomp•●◯ = ●.precomp-η-≃ ●.isModal●
