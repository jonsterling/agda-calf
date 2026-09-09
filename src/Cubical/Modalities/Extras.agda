open import Cubical.Foundations.Prelude
open import Cubical.Modalities.Modality

module Cubical.Modalities.Extras {ℓ : Level} (M : Modality ℓ) where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
  using (equivAdjointEquiv)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
  using (PathP≡Path⁻; PathP≃Path; compPathlEquiv; compPathrEquiv)
open import Cubical.Foundations.Univalence using (isEquivTransport)
open import Cubical.Data.Sigma

open Modality M

private
  variable X Y Z : Type ℓ

-- basic monadic utilities
module _ where
  map : (X → Y) → ◯ X → ◯ Y
  map = ◯-map

  map-∘ : (f : X → Y) (g : Y → Z) (x◦ : ◯ X) →
    map g (map f x◦) ≡ map (g ∘ f) x◦
  map-∘ f g = ◯-elim (λ _ → ◯-=-isModal _ _)
    λ x → cong (map g) (◯-map-β f x) ∙ ◯-map-β g (f x) ∙ sym (◯-map-β (g ∘ f) x)

  join : ◯ (◯ X) → ◯ X
  join = ◯-rec ◯-isModal (idfun _)

  join-β : (x◦ : ◯ X) → join (η x◦) ≡ x◦
  join-β = ◯-rec-β ◯-isModal (idfun _)

  bind : ◯ X → (X → ◯ Y) → ◯ Y
  bind x◦ k = join (map k x◦)

  η-isNatural : (f : X → Y) → η ∘ f ≡ map f ∘ η
  η-isNatural f = funExt λ x → sym (◯-map-β f x)

  map-η≡η : map (η {X}) ≡ η
  map-η≡η = funExt (◯-elim (λ _ → ◯-=-isModal _ _) (◯-map-β η))

-- ○Σ○ is equivalent to ○Σ
module _ {X : Type ℓ} {Y : X → Type ℓ} where
  ○Σ○≃○Σ : ◯ (Σ X (◯ ∘ Y)) ≃ ◯ (Σ X Y)
  ○Σ○≃○Σ = isoToEquiv (iso bwd fwd bwd-fwd fwd-bwd)
    where
      fwd₀ : Σ X Y → Σ X (◯ ∘ Y)
      fwd₀ (x , y) = x , η y

      fwd : ◯ (Σ X Y) → ◯ (Σ X (◯ ∘ Y))
      fwd = map fwd₀

      bwd₀ : Σ X (◯ ∘ Y) → ◯ (Σ X Y)
      bwd₀ (x , y◦) = map (x ,_) y◦

      bwd : ◯ (Σ X (◯ ∘ Y)) → ◯ (Σ X Y)
      bwd = ◯-rec ◯-isModal bwd₀

      bwd-fwd : ∀ w → bwd (fwd w) ≡ w
      bwd-fwd = ◯-elim (λ _ → ◯-=-isModal _ _) λ (x , y) →
          cong bwd (◯-map-β fwd₀ (x , y))
        ∙ ◯-rec-β ◯-isModal bwd₀ (x , η y)
        ∙ ◯-map-β (x ,_) y

      lemma : ∀ x (y◦ : ◯ (Y x)) → map (λ y → x , η y) y◦ ≡ η (x , y◦)
      lemma x = ◯-elim (λ _ → ◯-=-isModal _ _) λ y → ◯-map-β (λ y → x , η y) y

      fwd-bwd : ∀ w → fwd (bwd w) ≡ w
      fwd-bwd = ◯-elim (λ _ → ◯-=-isModal _ _) λ (x , y◦) →
          cong fwd (◯-rec-β ◯-isModal bwd₀ (x , y◦))
        ∙ map-∘ (x ,_) fwd₀ y◦
        ∙ lemma x y◦

-- isModal (inherited) and isConnected
module _ where
  isConnected : Type ℓ → Type ℓ
  isConnected X = isContr (◯ X)

  isModalMap : (X → Y) → Type ℓ
  isModalMap {Y = Y} f = (y : Y) → isModal (fiber f y)

  isConnectedMap : (X → Y) → Type ℓ
  isConnectedMap {Y = Y} f = (y : Y) → isConnected (fiber f y)

-- lemmas about isModal
module _ where
  isModalΣ : {Y : X → Type ℓ}
    → isModal X
    → ((x : X) → isModal (Y x))
    → isModal (Σ X Y)
  isModalΣ = Σ-isModal _

  opaque
    isModal-≃ : X ≃ Y → isModal X → isModal Y
    isModal-≃ = equivPreservesIsModal

  isModalIsProp : isModal X → isModal (isProp X)
  isModalIsProp w = Π-isModal λ _ → Π-isModal λ _ → isModal≡ w

  opaque
    isModalPathP : {X : I → Type ℓ} → isModal (X i0) → ∀ {x x'} → isModal (PathP X x x')
    isModalPathP {X = X} h {x} {x'} =
      subst isModal (sym (PathP≡Path⁻ X x x')) (isModal≡ h)

  η-ext : {Y : ◯ X → Type ℓ} (_ : (x◦ : ◯ X) → isModal (Y x◦))
    {y y' : (x◦ : ◯ X) → Y x◦} → y ∘ η ≡ y' ∘ η → y ≡ y'
  η-ext y p = funExt (◯-elim (λ x◦ → isModal≡ (y x◦)) (funExt⁻ p))

  ◯-rec-unique : {f : X → Y} (isModalY : isModal Y) {h : ◯ X → Y}
    → h ∘ η ≡ f → h ≡ ◯-rec isModalY f
  ◯-rec-unique isModalY p =
    η-ext (λ _ → isModalY) (p ∙ sym (funExt (◯-rec-β isModalY _)))

  η-=-isModal : {x x' : X} → isModal (η x ≡ η x')
  η-=-isModal {X} {x} {x'} = ◯-=-isModal (η x) (η x')

-- lemmas about ◯-rec
module _ where
  ◯-rec-map : (isModalZ : isModal Z) (g : Y → Z) (h : X → Y) (x◦ : ◯ X)
    → ◯-rec isModalZ g (map h x◦) ≡ ◯-rec isModalZ (g ∘ h) x◦
  ◯-rec-map isModalZ g h =
    funExt⁻ $ η-ext (λ _ → isModalZ) $ funExt λ x →
      cong (◯-rec isModalZ g) (◯-map-β h x)
    ∙ ◯-rec-β isModalZ g (h x) ∙ sym (◯-rec-β isModalZ (g ∘ h) x)

  ◯-rec-const : (isModalZ : isModal Y) (y : Y) (x◦ : ◯ X) → ◯-rec isModalZ (λ _ → y) x◦ ≡ y
  ◯-rec-const isModalZ y =
    funExt⁻ (η-ext (λ _ → isModalZ) (funExt (◯-rec-β isModalZ (λ _ → y))))

-- lemmas about isConnected
module _ where
  opaque
    isConnected-≃ : X ≃ Y → isConnected X → isConnected Y
    isConnected-≃ e = isOfHLevelRespectEquiv 0 (◯-equiv e)

  opaque
    isConnectedΣ : {Y : X → Type ℓ}
      → isConnected X
      → ((x : X) → isConnected (Y x))
      → isConnected (Σ X Y)
    isConnectedΣ cX cY =
      isOfHLevelRespectEquiv 0 ○Σ○≃○Σ
        (isConnected-≃ (invEquiv (Σ-contractSnd cY)) cX)

  isConnectedMapη : isConnectedMap (η {X})
  isConnectedMapη {X} y = center y , contract y
    where
      center : (y : ◯ X) → ◯ (fiber η y)
      center = ◯-elim (λ _ → ◯-isModal) (λ x → η (x , refl))

      contract : (y : ◯ X) (w : ◯ (fiber η y)) → center y ≡ w
      contract y = ◯-elim (λ _ → ◯-=-isModal _ _)
        (λ (x , p) → J (λ y' p' → center y' ≡ η (x , p'))
          (◯-elim-β (λ _ → ◯-isModal) (λ x → η (x , refl)) x)
          p)

  opaque
    isContr→isConnected : isContr X → isConnected X
    isContr→isConnected (x , contr) =
      η x , ◯-elim (λ _ → ◯-=-isModal _ _) (cong η ∘ contr)

  opaque
    isEquiv→isConnectedMap : {f : X → Y} → isEquiv f → isConnectedMap f
    isEquiv→isConnectedMap f-equiv y = isContr→isConnected (f-equiv .equiv-proof y)

  opaque
    isConnectedMap-∘ₑ : (e : Y ≃ Z) {f : X → Y}
      → isConnectedMap f → isConnectedMap (equivFun e ∘ f)
    isConnectedMap-∘ₑ e {f} conn z =
      isConnected-≃
        (Σ-cong-equiv-snd λ x → equivAdjointEquiv e)
        (conn (invEq e z))

  map-Σ : {X X' : Type ℓ} {Y : X → Type ℓ} {Y' : X' → Type ℓ}
    (f : X → X') → ((x : X) → Y x → Y' (f x))
    → Σ X Y → Σ X' Y'
  map-Σ f g (x , y) = f x , g x y

  opaque
    isConnectedMapΣ : {X X' : Type ℓ} {Y : X → Type ℓ} {Y' : X' → Type ℓ}
      {f : X → X'} {g : (x : X) → Y x → Y' (f x)}
      → isConnectedMap f → ((x : X) → isConnectedMap (g x))
      → isConnectedMap (map-Σ {Y' = Y'} f g)
    isConnectedMapΣ {X} {X'} {Y} {Y'} {f} {g} f-conn g-conn (x' , y') =
      isConnected-≃ (invEquiv e)
        (isConnectedΣ (f-conn x') λ (x , h) →
          isConnectedMap-∘ₑ
            (transport (λ i → Y' (h i)) , isEquivTransport (λ i → Y' (h i)))
            (g-conn x)
            y')
      where
        e : fiber (map-Σ {Y' = Y'} f g) (x' , y')
          ≃ (Σ[ (x , h) ∈ fiber f x' ] fiber (transport (λ i → Y' (h i)) ∘ g x) y')
        e =
            fiber (map-Σ {Y' = Y'} f g) (x' , y')
          ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv ΣPath≃PathΣ) ⟩
            (Σ[ (x , y) ∈ Σ X Y ] Σ[ h ∈ f x ≡ x' ]
              PathP (λ i → Y' (h i)) (g x y) y')
          ≃⟨ Σ-assoc-≃ ⟩
            (Σ[ x ∈ X ] Σ[ y ∈ Y x ] Σ[ h ∈ f x ≡ x' ]
              PathP (λ i → Y' (h i)) (g x y) y')
          ≃⟨ Σ-cong-equiv-snd (λ x →
                 invEquiv Σ-assoc-≃
               ∙ₑ invEquiv (Σ-cong-equiv-fst Σ-swap-≃)
               ∙ₑ Σ-assoc-≃) ⟩
            (Σ[ x ∈ X ] Σ[ h ∈ f x ≡ x' ] Σ[ y ∈ Y x ]
              PathP (λ i → Y' (h i)) (g x y) y')
          ≃⟨ invEquiv Σ-assoc-≃ ⟩
            (Σ[ (x , h) ∈ fiber f x' ] Σ[ y ∈ Y x ]
              PathP (λ i → Y' (h i)) (g x y) y')
          ≃⟨ Σ-cong-equiv-snd (λ (x , h) → Σ-cong-equiv-snd λ y →
               PathP≃Path (λ i → Y' (h i)) (g x y) y') ⟩
            (Σ[ (x , h) ∈ fiber f x' ] fiber (transport (λ i → Y' (h i)) ∘ g x) y')
          ■

-- isModal + isConnected
module _ where
  opaque
    isModal+isConnected→isContr : isModal X → isConnected X → isContr X
    isModal+isConnected→isContr X-modal =
      isOfHLevelRespectEquiv 0 (invEquiv (η , isModalToIsEquiv X-modal))

  opaque
    isModal+isConnected→isEquiv : {f : X → Y}
      → isModalMap f → isConnectedMap f → isEquiv f
    isModal+isConnected→isEquiv f-modal f-connected .equiv-proof y =
      isModal+isConnected→isContr (f-modal y) (f-connected y)

-- reflection-≃
module _ where
  reflection-inv : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
    → Y → ◯ X
  reflection-inv w conn y = map fst (conn y .fst)

  opaque
    reflection-sec : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
      → section (◯-rec w f) (reflection-inv w conn)
    reflection-sec {f = f} w conn y =
        ◯-rec-map w f fst (conn y .fst)
      ∙ cong (λ k → ◯-rec w k (conn y .fst)) (funExt snd)
      ∙ ◯-rec-const w y (conn y .fst)

  opaque
    reflection-ret : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
      → retract (◯-rec w f) (reflection-inv w conn)
    reflection-ret {f = f} w conn = funExt⁻ (η-ext (λ _ → ◯-isModal) (funExt λ x →
        cong (reflection-inv w conn) (◯-rec-β w f x)
      ∙ cong (map fst) (conn (f x) .snd (η (x , refl)))
      ∙ ◯-map-β fst (x , refl)))

  reflection-isEquiv : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f)
    → isEquiv (◯-rec w f)
  reflection-isEquiv {f = f} w conn =
    isoToIsEquiv
      (iso (◯-rec w f) (reflection-inv w conn)
        (reflection-sec w conn) (reflection-ret w conn))

  opaque
    precomp-η-isEquiv : (w : isModal Y) → isEquiv (λ (h : ◯ X → Y) → h ∘ η)
    precomp-η-isEquiv w = isoToIsEquiv (iso (_∘ η) (◯-rec w)
      (λ k → funExt (◯-rec-β w k))
      (λ h → η-ext (λ _ → w) (funExt (◯-rec-β w (h ∘ η)))))

  precomp-η-≃ : isModal Y → (◯ X → Y) ≃ (X → Y)
  precomp-η-≃ w = (_∘ η) , precomp-η-isEquiv w

  opaque
    reflection-≃ : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f) → ◯ X ≃ Y
    reflection-≃ {f = f} w conn = ◯-rec w f , reflection-isEquiv w conn

    reflection-β : {f : X → Y} (w : isModal Y) (conn : isConnectedMap f) (x : X)
      → equivFun (reflection-≃ w conn) (η x) ≡ f x
    reflection-β {f = f} w conn = ◯-rec-β w f

  opaque
    reflection-connected : {f : X → Y} (w : isModal Y)
      → isEquiv (◯-rec w f) → isConnectedMap f
    reflection-connected {f = f} w h =
      subst isConnectedMap (funExt (◯-rec-β w f))
        (isConnectedMap-∘ₑ (◯-rec w f , h) isConnectedMapη)

module _ {X : Type ℓ} {Y : ◯ X → Type ℓ} (w : (x◦ : ◯ X) → isModal (Y x◦)) where
  private
    c-connected : isConnectedMap (map-Σ {Y' = Y} η (λ x → idfun (Y (η x))))
    c-connected =
      isConnectedMapΣ isConnectedMapη λ x → isEquiv→isConnectedMap (idIsEquiv (Y (η x)))

  ◯Σ-modal : ◯ (Σ X (Y ∘ η)) ≃ Σ (◯ X) Y
  ◯Σ-modal = reflection-≃ (isModalΣ ◯-isModal w) c-connected

  ◯Σ-modal-β : (x : X) (y : Y (η x))
    → equivFun ◯Σ-modal (η (x , y)) ≡ (η x , y)
  ◯Σ-modal-β x y = reflection-β (isModalΣ ◯-isModal w) c-connected (x , y)

IsLex◯ : Type _
IsLex◯ = {X : Type ℓ} {x x' : X} → isEquiv (◯-rec (◯-=-isModal (η x) (η x')) (cong η))

-- consequences of lexness
module _ (lex : IsLex◯) where
  opaque
    ≡-connected : isConnected X → {x y : X} → isConnected (x ≡ y)
    ≡-connected cX {x} {y} =
      isOfHLevelRespectEquiv 0 (invEquiv (_ , lex))
        (isContr→isContrPath cX (η x) (η y))

  opaque
    isConnectedPathP : {X : I → Type ℓ} → isConnected (X i0) → ∀ {x x'} → isConnected (PathP X x x')
    isConnectedPathP {X = X} cX {x} {x'} =
      subst isConnected (sym (PathP≡Path⁻ X x x')) (≡-connected cX)

  opaque
    isSet◯-lex : isSet X → isSet (◯ X)
    isSet◯-lex {X = X} isSetX =
      ◯-elim (λ x◦ → Π-isModal λ x◦' → isProp≡-modal x◦ x◦') λ x →
      ◯-elim (isProp≡-modal (η x)) λ x' →
      isOfHLevelRespectEquiv 1 (_ , lex) (◯-preservesProp (isSetX x x'))
      where
        isProp≡-modal : (x◦ x◦' : ◯ X) → isModal (isProp (x◦ ≡ x◦'))
        isProp≡-modal x◦ x◦' =
          Π-isModal λ _ → Π-isModal λ _ → isModal≡ (◯-=-isModal x◦ x◦')

  ◯-≡-≃ : {x x' : X} → ◯ (x ≡ x') ≃ (η x ≡ η x')
  ◯-≡-≃ = _ , lex

  module _ {X Y Z : Type ℓ} {f : X → Z} {g : Y → Z} where
    private
      pe : (x : X) (y : Y) → ◯ (f x ≡ g y) ≃ (map f (η x) ≡ map g (η y))
      pe x y = ◯-≡-≃ ∙ₑ compPathrEquiv (sym (◯-map-β g y)) ∙ₑ compPathlEquiv (◯-map-β f x)

      Pullback◯-isModal : isModal (Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦))
      Pullback◯-isModal =
        isModalΣ (isModalΣ ◯-isModal λ _ → ◯-isModal) λ _ → ◯-=-isModal _ _

    pullback-η
      : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y)
      → Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦)
    pullback-η = map-Σ (map-Σ η λ _ → η) λ (x , y) → equivFun (pe x y) ∘ η

    pullback-η-connected : isConnectedMap pullback-η
    pullback-η-connected =
      isConnectedMapΣ
        (isConnectedMapΣ isConnectedMapη λ _ → isConnectedMapη)
        (λ (x , y) → isConnectedMap-∘ₑ (pe x y) isConnectedMapη)

    opaque
      ◯-pullback-lex
        : ◯ (Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
        ≃ (Σ[ (x◦ , y◦) ∈ ◯ X × ◯ Y ] (map f x◦ ≡ map g y◦))
      ◯-pullback-lex = reflection-≃ Pullback◯-isModal pullback-η-connected

      ◯-pullback-lex-β
        : (u : Σ[ (x , y) ∈ X × Y ] (f x ≡ g y))
        → equivFun ◯-pullback-lex (η u) ≡ pullback-η u
      ◯-pullback-lex-β = reflection-β Pullback◯-isModal pullback-η-connected
