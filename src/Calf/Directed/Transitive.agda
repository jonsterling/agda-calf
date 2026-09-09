module Calf.Directed.Transitive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[f∘equivFunA≃B]→isEquiv[f])
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization
open import Relation.Binary.Definitions using (Transitive)

open import Calf.Core.Interval
open import Calf.Directed.Path
open import Calf.Directed.Thin

open import Cubical.HITs.Pushout public

private variable X Y : Type

isTransitive : Type → Type
isTransitive X = Transitive (_⊑_ {X})

Λ² : Type
Λ² = Pushout {A = Unit} (const 1𝟚) (const 0𝟚)

Δ² : Type
Δ² =
  Pushout {A = Bool} {B = Λ²} {C = 𝟚}
    (λ { false → inl 0𝟚 ; true → inr 1𝟚 })
    (λ { false → 0𝟚 ; true → 1𝟚 })

ι-horn : Λ² → Δ²
ι-horn = inl

open Iso

Δ²-elim : Iso (Δ² → X) (Σ[ h ∈ (Λ² → X) ] (h (inl 0𝟚) ⊑ h (inr 1𝟚)))
Δ²-elim .fun k =
  (k ∘ inl) , (k ∘ inr) , cong k (sym (push false)) , cong k (sym (push true))
Δ²-elim .inv (h , e) (inl b) = h b
Δ²-elim .inv (h , e) (inr 𝕚) = path e 𝕚
Δ²-elim .inv (h , e) (push false i) = sym (path₀ e) i
Δ²-elim .inv (h , e) (push true i) = sym (path₁ e) i
Δ²-elim .rightInv (h , e) = refl
Δ²-elim .leftInv k i (inl b) = k (inl b)
Δ²-elim .leftInv k i (inr 𝕚) = k (inr 𝕚)
Δ²-elim .leftInv k i (push false j) = k (push false j)
Δ²-elim .leftInv k i (push true j) = k (push true j)

Λ²-elim : Iso (Λ² → X) (Σ[ p ∈ (𝟚 → X) ] Σ[ q ∈ (𝟚 → X) ] (p 1𝟚 ≡ q 0𝟚))
Λ²-elim .fun k = (k ∘ inl) , (k ∘ inr) , cong k (push tt)
Λ²-elim .inv (p , q , r) (inl 𝕚) = p 𝕚
Λ²-elim .inv (p , q , r) (inr 𝕚) = q 𝕚
Λ²-elim .inv (p , q , r) (push tt j) = r j
Λ²-elim .rightInv _ = refl
Λ²-elim .leftInv k i (inl 𝕚) = k (inl 𝕚)
Λ²-elim .leftInv k i (inr 𝕚) = k (inr 𝕚)
Λ²-elim .leftInv k i (push tt j) = k (push tt j)

isPathTransitive : Type → Type
isPathTransitive = isLocal {A = Unit} (const ι-horn)

isEquivFst→isContrFibers : {B : Type} {P : B → Type}
  → isEquiv (fst {A = B} {B = P}) → (b : B) → isContr (P b)
isEquivFst→isContrFibers {P = P} e b =
  isOfHLevelRespectEquiv 0 (invEquiv (fiberProjEquiv _ P b)) (e .equiv-proof b)

isPathTransitive→fillers : isPathTransitive X → (h : Λ² → X) → isContr (h (inl 0𝟚) ⊑ h (inr 1𝟚))
isPathTransitive→fillers pt =
  isEquivFst→isContrFibers
    (isEquiv[f∘equivFunA≃B]→isEquiv[f] fst (isoToEquiv Δ²-elim) (toIsEquiv _ (pt tt)))

isPathTransitive→isTransitive : isPathTransitive X → isTransitive X
isPathTransitive→isTransitive pt e f =
  ≡∙⊑ (sym (path₀ e)) (⊑∙≡ (isPathTransitive→fillers pt horn .fst) (path₁ f))
  where horn = Λ²-elim .inv (path e , path f , path₁ e ∙ sym (path₀ f))

isThin∧isTransitive→isPathTransitive :
  isThin X → isTransitive X → isPathTransitive X
isThin∧isTransitive→isPathTransitive {X} ⊑prop ⊑trans _ =
  fromIsEquiv _ (compEquiv (isoToEquiv Δ²-elim) (Σ-contractSnd edge) .snd)
  where
    composite : (h : Λ² → X) → h (inl 0𝟚) ⊑ h (inr 1𝟚)
    composite h =
      ⊑trans (h ∘ inl , refl , refl) $
      ≡∙⊑ (cong h (push tt)) $
      (h ∘ inr , refl , refl)

    edge : (h : Λ² → X) → isContr (h (inl 0𝟚) ⊑ h (inr 1𝟚))
    edge h = composite h , ⊑prop _ _ (composite h)

isThin→isPathTransitive≡isTransitive :
  isThin X → isPathTransitive X ≡ isTransitive X
isThin→isPathTransitive≡isTransitive {X} isThinX =
  hPropExt
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    isPropIsTransitive
    isPathTransitive→isTransitive
    (isThin∧isTransitive→isPathTransitive isThinX)
  where
    isPropIsTransitive : isProp (isTransitive X)
    isPropIsTransitive t t' i a b = isThinX _ _ (t a b) (t' a b) i
