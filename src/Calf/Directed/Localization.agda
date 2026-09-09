open import Cubical.Foundations.Prelude

module Calf.Directed.Localization
  {A : Type} {S : A → Type} {T : A → Type} {F : ∀ α → S α → T α}
  where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Localization
open import Cubical.HITs.Nullification.Properties using (toPathP⁻-sq)

open import Calf.Core.Interval using (𝟚; 0𝟚; 1𝟚)
open import Calf.Directed.Path using (_⊑_; path; path₀; path₁)

private variable X Y Z : Type

open isPathSplitEquiv
open Iso

isProp→isLocal : ((α : A) → S α) → isProp X → isLocal F X
isProp→isLocal {X} s isPropX α =
  fromIsEquiv _ $ isoToIsEquiv $
  iso
    (λ g → g ∘ F α)
    (λ h _ → h (s α))
    (λ _ → isPropΠ (λ _ → isPropX) _ _)
    (λ _ → isPropΠ (λ _ → isPropX) _ _)

isLocalRetract : (s : Y → X) (r : X → Y) → retract s r → isLocal F X → isLocal F Y
isLocalRetract {Y} {X} s r ret isLocalX α =
  fromIsEquiv _ $ isoToIsEquiv $
  iso
    (_∘ F α)
    (λ h → r ∘ isoX .inv (s ∘ h))
    (λ h → cong (r ∘_) (isoX .rightInv (s ∘ h)) ∙ funExt (ret ∘ h))
    (λ g → cong (r ∘_) (isoX .leftInv (s ∘ g)) ∙ funExt (ret ∘ g))
  where
    isoX : Iso (T α → X) (S α → X)
    isoX = toIso (_∘ F α) (isLocalX α)

isLocalPathFun :
  isLocal F Y → (α : A) (P₀ P₁ : T α → Y)
  → isPathSplitEquiv (λ (b : (t : T α) → P₀ t ≡ P₁ t) → b ∘ F α)
isLocalPathFun isLocalY α P₀ P₁ =
  fromIsEquiv _ $
  isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ b → b ∘ F α) funExtEquiv $
  equivIsEquiv $
    compEquiv funExtEquiv $
    congEquiv ((λ k → k ∘ F α) , toIsEquiv _ (isLocalY α))

isLocal≡ : isLocal F Y → {x y : Y} → isLocal F (x ≡ y)
isLocal≡ isLocalY {x} {y} α = isLocalPathFun isLocalY α (λ _ → x) (λ _ → y)

rec-unique :
  isLocal F Y
  → (f g : Localize F X → Y)
  → ((x : X) → f ∣ x ∣ ≡ g ∣ x ∣)
  → (z : Localize F X) → f z ≡ g z
rec-unique {X = X} isLocalY f g p = elim
  where
    elim : (z : Localize F X) → f z ≡ g z

    Q : Localize F X → Type
    Q z = f z ≡ g z

    K : (α : A) (w : S α → Localize F X) → (f ∘ ext α w) ∘ F α ≡ (g ∘ ext α w) ∘ F α
    K α w = funExt (λ s → cong f (isExt α w s) ∙ elim (w s) ∙ cong g (sym (isExt α w s)))

    secCongDep′ :
      (α : A) {u v : T α → Localize F X} (E : u ≡ v)
      (bx : (t : T α) → Q (u t)) (by : (t : T α) → Q (v t))
      → hasSection
          (λ (P : PathP (λ i → (t : T α) → Q (E i t)) bx by)
           → cong₂ (λ u (b : (t : T α) → Q (u t)) → b ∘ F α) E P)
    secCongDep′ α E =
      secCongDep
        (λ u (b : (t : T α) → Q (u t)) → b ∘ F α) E
        (λ u → secCong (isLocalPathFun isLocalY α (f ∘ u) (g ∘ u)))

    base : (α : A) (u v : T α → Localize F X) → ((s : S α) → u (F α s) ≡ v (F α s)) → u ≡ v
    base α u v q = funExt (λ t → ≡ext α u v q t)

    endpoint : (α : A) (u : T α → Localize F X) (t : T α) → Q (u t)
    endpoint α u t = transport refl (elim (u t))

    input :
      (α : A) (u v : T α → Localize F X) (q : (s : S α) → u (F α s) ≡ v (F α s))
      → PathP (λ i → (s : S α)
      → Q (≡ext α u v q (F α s) i)) (endpoint α u ∘ F α) (endpoint α v ∘ F α)
    input α u v q i s = transport (λ k → Q (≡isExt α u v q s (~ k) i)) (elim (q s i))

    elim ∣ x ∣ = p x
    elim (ext α w t) =
      funExt⁻ (secCong (isLocalY α) (f ∘ ext α w) (g ∘ ext α w) .fst (K α w)) t
    elim (isExt α w s i) =
      compPathR→PathP
        (λ i' → funExt⁻ (secCong (isLocalY α) (f ∘ ext α w) (g ∘ ext α w) .snd (K α w) i') s) i
    elim (≡ext α u v q t i) =
      hcomp (λ k → λ { (i = i0) → transportRefl (elim (u t)) k
                     ; (i = i1) → transportRefl (elim (v t)) k })
            (secCongDep′ α (base α u v q) (endpoint α u) (endpoint α v) .fst (input α u v q) i t)
    elim (≡isExt α u v q s i j) =
      hcomp (λ k → λ { (j = i0) → toPathP⁻-sq (elim (u (F α s))) k i
                     ; (j = i1) → toPathP⁻-sq (elim (v (F α s))) k i
                     ; (i = i1) → elim (q s j) })
            (toPathP⁻ {A = λ i' → Q (≡isExt α u v q s i' j)}
                      (λ i' → secCongDep′ α (base α u v q) (endpoint α u) (endpoint α v) .snd (input α u v q) i' j s)
                      i)

opaque
  isLocalUnit : isLocal F Unit
  isLocalUnit α =
    fromIsEquiv _ $ equivIsEquiv $
    isContr→Equiv (isContrΠ λ _ → isContrUnit) (isContrΠ λ _ → isContrUnit)

opaque
  isLocal× : isLocal F X → isLocal F Y → isLocal F (X × Y)
  isLocal× {X} {Y} isLocalX isLocalY α = fromIsEquiv _ (equivIsEquiv equiv)
    where
      equiv : (T α → X × Y) ≃ (S α → X × Y)
      equiv =
        (T α → X × Y)         ≃⟨ Σ-Π-≃ ⟩
        (T α → X) × (T α → Y) ≃⟨ ≃-× (_ , toIsEquiv _ (isLocalX α)) (_ , toIsEquiv _ (isLocalY α)) ⟩
        (S α → X) × (S α → Y) ≃⟨ invEquiv Σ-Π-≃ ⟩
        (S α → X × Y)         ■

opaque
  isLocalΠ : {Y : X → Type} → ((x : X) → isLocal F (Y x)) → isLocal F ((x : X) → Y x)
  isLocalΠ {X} {Y} isLocalY α = fromIsEquiv _ (equivIsEquiv equiv)
    where
      flip≃ : (W : Type) → (W → (x : X) → Y x) ≃ ((x : X) → W → Y x)
      flip≃ W = isoToEquiv (iso flip flip (λ _ → refl) (λ _ → refl))

      equiv : (T α → (x : X) → Y x) ≃ (S α → (x : X) → Y x)
      equiv =
        (T α → (x : X) → Y x) ≃⟨ flip≃ (T α) ⟩
        ((x : X) → T α → Y x) ≃⟨ equivΠCod (λ x → _ , toIsEquiv _ (isLocalY x α)) ⟩
        ((x : X) → S α → Y x) ≃⟨ invEquiv (flip≃ (S α)) ⟩
        (S α → (x : X) → Y x) ■

opaque
  isLocalEqualizer :
    isLocal F X → isLocal F Y → (φ ψ : X → Y)
    → isLocal F (Σ[ x ∈ X ] φ x ≡ ψ x)
  isLocalEqualizer {X} {Y} isLocalX isLocalY φ ψ α = fromIsEquiv _ (equivIsEquiv equiv)
    where
      equiv : (T α → Σ[ x ∈ X ] φ x ≡ ψ x) ≃ (S α → Σ[ x ∈ X ] φ x ≡ ψ x)
      equiv =
          (T α → Σ[ x ∈ X ] φ x ≡ ψ x)
        ≃⟨ Σ-Π-≃ ⟩
          Σ[ g ∈ (T α → X) ] ((t : T α) → φ (g t) ≡ ψ (g t))
        ≃⟨
          Σ-cong-equiv
            (_ , toIsEquiv _ (isLocalX α))
            (λ g → _ , toIsEquiv _ (isLocalPathFun isLocalY α (φ ∘ g) (ψ ∘ g)))
        ⟩
          Σ[ h ∈ (S α → X) ] ((s : S α) → φ (h s) ≡ ψ (h s))
        ≃⟨ invEquiv Σ-Π-≃ ⟩
          (S α → Σ[ x ∈ X ] φ x ≡ ψ x)
        ■

opaque
  isLocalPullback :
    isLocal F X → isLocal F Y → isLocal F Z → (f : X → Z) (g : Y → Z)
    → isLocal F (Σ[ (x , y) ∈ X × Y ] f x ≡ g y)
  isLocalPullback isLocalX isLocalY isLocalZ f g =
    isLocalEqualizer (isLocal× isLocalX isLocalY) isLocalZ (λ (x , y) → f x) (λ (x , y) → g y)

opaque
  isLocalComma :
    isLocal F X → isLocal F Y → isLocal F Z → {f : X → Z} {g : Y → Z}
    → isLocal F (Σ[ (x , y) ∈ X × Y ] f x ⊑ g y)
  isLocalComma isLocalX isLocalY isLocalZ {f} {g} =
    isLocalRetract
      (λ ((x , y) , q) → ((x , y) , path q) , λ i → path₀ q i , path₁ q i)
      (λ (((x , y) , p) , e) → (x , y) , p , cong fst e , cong snd e)
      (λ _ → refl)
      (isLocalEqualizer
        (isLocal× (isLocal× isLocalX isLocalY) (isLocalΠ λ _ → isLocalZ))
        (isLocal× isLocalZ isLocalZ)
        (λ ((x , y) , p) → p 0𝟚 , p 1𝟚)
        (λ ((x , y) , p) → f x , g y))

opaque
  isLocalΣ : {Y : X → Type}
    → isLocal F X
    → ((α : A) → isEquiv (const {A = X} {B = T α}))
    → ((x : X) → isLocal F (Y x))
    → isLocal F (Σ X Y)
  isLocalΣ {X} {Y} isLocalX nullT isLocalY α = fromIsEquiv _ (equivIsEquiv equiv)
    where
      fiber-isEquiv : (f : T α → X) → isEquiv (λ (h : (t : T α) → Y (f t)) → h ∘ F α)
      fiber-isEquiv f =
        subst (λ f' → isEquiv (λ (h : (t : T α) → Y (f' t)) → h ∘ F α))
          (secEq (const , nullT α) f)
          (toIsEquiv _ (isLocalY (invEq (const , nullT α) f) α))

      equiv : (T α → Σ X Y) ≃ (S α → Σ X Y)
      equiv =
          (T α → Σ X Y)
        ≃⟨ Σ-Π-≃ ⟩
          Σ[ f ∈ (T α → X) ] ((t : T α) → Y (f t))
        ≃⟨ Σ-cong-equiv (_ , toIsEquiv _ (isLocalX α)) (λ f → _ , fiber-isEquiv f) ⟩
          Σ[ g ∈ (S α → X) ] ((s : S α) → Y (g s))
        ≃⟨ invEquiv Σ-Π-≃ ⟩
          (S α → Σ X Y)
        ■
