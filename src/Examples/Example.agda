{-# OPTIONS --prop --rewriting #-}

module Examples.Example where

open import Calf
open import Calf.Types.Bool
import Relation.Binary.PropositionalEquality as P

boolc : tp pos
boolc = ► bool

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
lam _ β M = ret λ x → ▷/ret (F [ β ]) (M x)

app : (α β : 𝒱) → ⊢ α ⇒ β → ⊢ α → ⊢ β
app α β M N =
  bind (F [ β ]) N λ x →
  bind (F _) M λ f →
  ▷/match (F [ β ]) (f x) (λ z → z)

tt : ⊢ 𝔹
tt = ret (►/ret _ true)

ff : ⊢ 𝔹
ff = ret (►/ret _ false)

not : ⊢ 𝔹 ⇒ 𝔹
not =
  lam 𝔹 𝔹 λ x →
  ►/match (F [ 𝔹 ]) x λ where
    true → ff
    false → tt

notnot : ⊢ 𝔹 ⇒ 𝔹
notnot = lam 𝔹 𝔹 (λ x → app 𝔹 𝔹 not (app 𝔹 𝔹 not (ret x)))

foo : ◯ (notnot ≡ lam 𝔹 𝔹 (λ x → ret x))
foo z =
  let unstep = λ x → step/ext (F boolc) x z in
  P.cong ret
   (funext
    (►/ind z λ where
     true → P.cong (▷/ret _) (P.trans (unstep _) (P.trans (unstep _) (P.trans (unstep _) (unstep _))))
     false → P.cong (▷/ret _) (P.trans (unstep _) (P.trans (unstep _) (P.trans (unstep _) (unstep _))))))

_ : ∀ {α β f u} → app α β (lam α β f) (ret u) ≡ step (F [ β ]) (f u)
_ = refl
