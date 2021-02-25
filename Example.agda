{-# OPTIONS --prop --rewriting #-}

module Example where

open import Prelude
open import Metalanguage
open import CostEffect
open import PhaseDistinction

module Bool where
  data Bool : □ where tt ff : Bool
  postulate
    bool : tp pos
    bool/decode : val bool ≡ Bool
    {-# REWRITE bool/decode #-}

boolc : tp pos
boolc = ► Bool.bool


-- This version of the dependent product costs a step to apply.
-- One thing I noticed is that this version may not quite capture what I had in mind trying to force
-- the application to take a step.
Πc : (A : tp pos) (X : val A → tp neg) → tp neg
Πc A X = Π A λ x → ▷ (X x)

postulate
  𝒱 : □
  [_] : 𝒱 → tp pos
  _⇒_ : 𝒱 → 𝒱 → 𝒱
  𝔹 : 𝒱

  [⇒] : ∀ {α β} → [ α ⇒ β ] ≡ U (Πc [ α ] λ _ → F [ β ])
  [𝔹] : [ 𝔹 ] ≡ boolc
  {-# REWRITE [⇒] [𝔹] #-}

infix 10 ⊢_

⊢_ : 𝒱 → □
⊢ β = cmp (F [ β ])

_⊢_ : 𝒱 → 𝒱 → □
α ⊢ β = val [ α ] → ⊢ β

lam : (α β : 𝒱) → α ⊢ β → ⊢ α ⇒ β
lam _ β M = ret λ x → ▷/ret (F [ β ]) (M x) -- ▷/inv (M x)

app : (α β : 𝒱) → ⊢ α ⇒ β → ⊢ α → ⊢ β
app α β M N =
  bind (F [ β ]) N λ x →
  bind (F _) M λ f →
  ▷/match (F [ β ]) (f x) (λ z → z)

tt : ⊢ 𝔹
tt = ret (►/ret _ Bool.tt)

ff : ⊢ 𝔹
ff = ret (►/ret _ Bool.ff)

not : ⊢ 𝔹 ⇒ 𝔹
not =
  ret λ x →
  ▷/ret
   (F [ 𝔹 ])
   (►/match (F [ 𝔹 ]) x λ where
     Bool.tt → ff
     Bool.ff → tt)

notnot : ⊢ 𝔹 ⇒ 𝔹
notnot = lam 𝔹 𝔹 (λ x → app 𝔹 𝔹 not (app 𝔹 𝔹 not (ret x)))


match-unfold : ∀ {A} {P : val (► A) → □} → ◯ ((∀ x → P (►/ret _ x)) → ∀ x → P x)
match-unfold {A} {P} z f x rewrite (symm (►/ext/η z x))= f (►/ext A z x)

foo : ◯ (notnot ≡ lam 𝔹 𝔹 (λ x → ret x))
foo z =
  cong ret
   (funext
    (match-unfold z λ where
     Bool.tt → cong (▷/ret _) (trans (step/ext (F boolc) _ z) (trans (step/ext (F boolc) _ z) (trans (step/ext (F boolc) _ z) (step/ext (F boolc) _ z))))
     Bool.ff → cong (▷/ret _) (trans (step/ext (F boolc) _ z) (trans (step/ext (F boolc) _ z) (trans (step/ext (F boolc) _ z) (step/ext (F boolc) _ z))))))

test = app 𝔹 𝔹 not tt

_ : ∀ {α β f u} → app α β (lam α β f) (ret u) ≡ step (F [ β ]) (f u)
_ = refl
