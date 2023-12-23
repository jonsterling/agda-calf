{-# OPTIONS --rewriting --cubical #-}

module Examples.Abstraction where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Agda.Builtin.Cubical.Sub
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Level
open import Calf
open import Function

postulate
  extProp : hProp 0ℓ
ext = fst extProp
ext-isProp = snd extProp

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

◯ : Type ℓ → Type ℓ
◯ A = (u : ext) → A

data ● (A : Type ℓ) : Type ℓ where
  η : A → ● A
  ∗ : (u : ext) → ● A
  η≡∗ : (a : A) (u : ext) → η a ≡ ∗ u

unique : (a : ● A) → (u : ext) → a ≡ ∗ u
unique = {!   !}
-- unique (η x) u = η≡∗ x u
-- unique (∗ x) u = congS ∗ (ext-isProp x u)
-- unique (η≡∗ a u i) u' j = {!   !}

constant : (f : ● A → ◯ B) → Σ (◯ B) λ b → f ≡ const b
fst (constant f) u = f (∗ u) u
snd (constant f) i a u = congS (λ a → f a u) (unique a u) i


record Retract {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
    encode : A → B
    decode : B → A
    leftInv : retract encode decode

TypeWithGhost : {V : Type ℓ} {S : Type ℓ'} → Retract V S → Type (ℓ-max ℓ ℓ')
TypeWithGhost {V = V} {S = S} retr = Σ[ v ∈ ◯ V ] ● (Σ[ s ∈ S ] ((u : ext) → Retract.decode retr s ≡ v u))

record View {ℓ ℓ'} (V : Type ℓ) (S : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    encode : V → S
    decode : S → V
    leftInv  : retract encode decode
    rightInv : ext → section encode decode

foo : {V : Type ℓ} {S : Type ℓ'} → (retr : Retract V S) → View V (TypeWithGhost retr)
View.encode (foo retr) v = (λ _ → v) , η (Retract.encode retr v , λ _ → Retract.leftInv retr v)
View.decode (foo retr) (◯v , η (s , _)) = Retract.decode retr s
View.decode (foo retr) (◯v , ∗ u) = ◯v u
View.decode (foo retr) (◯v , η≡∗ (s , h) u i) = h u i
View.leftInv (foo retr) = Retract.leftInv retr
View.rightInv (foo retr) u (◯v , η (s , h)) = {!   !}
fst (View.rightInv (foo retr) u (◯v , ∗ u') i) = {! congS (λ u → ◯v u)  !}
snd (View.rightInv (foo retr) u (◯v , ∗ u') i) = {!   !}
View.rightInv (foo retr) u (◯v , η≡∗ a u' i) = {!   !}

-- viewToIso : ∀ {V S} → ◯ (View V S → Iso V S)
-- Iso.fun (viewToIso u view) = View.encode view
-- Iso.inv (viewToIso u view) = View.decode view
-- Iso.rightInv (viewToIso u view) = View.ext-iso view u
-- Iso.leftInv (viewToIso u view) = View.retract view

-- foo : ∀ {A} → isType A → isType (● A)
-- foo isType-A x x' h h' i i' = {!   !}


-- open import Calf.Data.Nat
-- open import Calf.Data.IsBounded costMonoid
-- open import Calf.Data.BigO costMonoid

-- open import Function using (_∘_; _$_)
-- open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning)


-- module Easy where
--   id : cmp (Π nat λ _ → F nat)
--   id n = ret n

--   id/bound : cmp (Π nat λ _ → F nat)
--   id/bound n = ret n

--   id/is-bounded : ∀ n → id n ≤⁻[ F nat ] id/bound n
--   id/is-bounded n = ≤⁻-refl

--   id/correct : ∀ n → ◯ (id n ≡ ret n)
--   id/correct n u = ≤⁻-ext-≡ u (id/is-bounded n)

--   id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → 0)
--   id/asymptotic = f[n]≤g[n]via (≤⁻-mono (λ e → bind (F _) e (λ _ → ret _)) ∘ id/is-bounded)


-- module Hard where
--   id : cmp (Π nat λ _ → F nat)
--   id zero = ret 0
--   id (suc n) =
--     step (F nat) 1 (
--       bind (F nat) (id n) λ n' →
--         ret (suc n')
--     )

--   id/bound : cmp (Π nat λ _ → F nat)
--   id/bound n = step (F nat) n (ret n)

--   id/is-bounded : ∀ n → id n ≤⁻[ F nat ] id/bound n
--   id/is-bounded zero    = ≤⁻-refl
--   id/is-bounded (suc n) =
--     let open ≤⁻-Reasoning (F nat) in
--     ≤⁻-mono (step (F nat) 1) $
--     begin
--       bind (F nat) (id n) (λ n' → ret (suc n'))
--     ≤⟨ ≤⁻-mono (λ e → bind (F nat) e (ret ∘ suc)) (id/is-bounded n) ⟩
--       bind (F nat) (step (F nat) n (ret n)) (λ n' → ret (suc n'))
--     ≡⟨⟩
--       step (F nat) n (ret (suc n))
--     ∎

--   id/correct : ∀ n → ◯ (id n ≡ ret n)
--   id/correct n u = Eq.trans (≤⁻-ext-≡ u (id/is-bounded n)) (step/ext (F nat) (ret n) n u)

--   id/asymptotic : given nat measured-via (λ n → n) , id ∈𝓞(λ n → n)
--   id/asymptotic = f[n]≤g[n]via (≤⁻-mono (λ e → bind (F _) e _) ∘ id/is-bounded)


-- easy≡hard : ◯ (Easy.id ≡ Hard.id)
-- easy≡hard u =
--   funext λ n →
--     begin
--       Easy.id n
--     ≡⟨ Easy.id/correct n u ⟩
--       ret n
--     ≡˘⟨ Hard.id/correct n u ⟩
--       Hard.id n
--     ∎
--       where open ≡-Reasoning
