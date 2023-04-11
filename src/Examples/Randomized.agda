{-# OPTIONS --prop --rewriting #-}

module Examples.Randomized where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid; ℤ-CostMonoid; ℚ-CostMonoid)

import Data.Nat
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; module ≡-Reasoning; _≢_)

open import Function using (_$_)


module Basic where

  costMonoid = ℕ-CostMonoid
  open CostMonoid costMonoid

  open import Calf costMonoid
  open import Calf.Probability costMonoid
  open import Calf.Types.Unit

  FLIP : 𝕀 → (e₀ e₁ : cmp (F unit)) → cmp (F unit)
  FLIP = flip (F unit)

  _+[_]_ : cmp (F unit) → 𝕀 → cmp (F unit) → cmp (F unit)
  e₀ +[ p ] e₁ = FLIP p e₀ e₁

  STEP : ℂ → cmp (F unit)
  STEP c = step (F unit) c (ret triv)

  foo : cmp (F unit)
  foo = FLIP ½ (FLIP ½ (STEP 100) (STEP 200)) (STEP 300)

  bar : cmp (F unit)
  bar = FLIP ¼ (FLIP ⅔ (STEP 100) (STEP 300)) (STEP 200)

  foo≡bar : foo ≡ bar
  foo≡bar =
    let open ≡-Reasoning in
    begin
      FLIP ½ (FLIP ½ (STEP 100) (STEP 200)) (STEP 300)
    ≡⟨ flip/sym (F unit) ½ (FLIP ½ (STEP 100) (STEP 200)) (STEP 300) ⟩
      FLIP ½ (STEP 300) (FLIP ½ (STEP 100) (STEP 200))
    ≡⟨ flip/assocˡ (F unit) (STEP 300) (STEP 100) (STEP 200) {p = ½} {q = ½} {r = ⅓} refl ⟩
      FLIP ¼ (FLIP ⅓ (STEP 300) (STEP 100)) (STEP 200)
    ≡⟨ Eq.cong (λ e → FLIP ¼ e (STEP 200)) (flip/sym (F unit) ⅓ (STEP 300) (STEP 100)) ⟩
      FLIP ¼ (FLIP ⅔ (STEP 100) (STEP 300)) (STEP 200)
    ∎

  foo≡bar' : foo ≡ bar
  foo≡bar' =
    let open ≡-Reasoning in
    begin
      (STEP 100 +[ ½ ] STEP 200) +[ ½ ] STEP 300
    ≡⟨ flip/sym (F unit) ½ (STEP 100 +[ ½ ] STEP 200) (STEP 300) ⟩
      FLIP ½ (STEP 300) (FLIP ½ (STEP 100) (STEP 200))
    ≡⟨ flip/assocˡ (F unit) (STEP 300) (STEP 100) (STEP 200) {p = ½} {q = ½} {r = ⅓} refl ⟩
      (STEP 300 +[ ⅓ ] STEP 100) +[ ¼ ] STEP 200
    ≡⟨ Eq.cong (λ e → e +[ ¼ ] STEP 200) (flip/sym (F unit) ⅓ (STEP 300) (STEP 100)) ⟩
      (STEP 100 +[ ⅔ ] STEP 300) +[ ¼ ] STEP 200
    ∎


module IteratedFlips where
  costMonoid = ℕ-CostMonoid
  open CostMonoid costMonoid

  open import Calf costMonoid
  open import Calf.Probability costMonoid
  open import Calf.Types.Bool
  open import Calf.Types.Nat

  nonzero-nonone : {p : 𝕀} → NonZero p → NonOne (1- p)
  nonzero-nonone h = {!   !}

  nonone-nonzero : {p : 𝕀} → NonOne p → NonZero (1- p)
  nonone-nonzero h = {!   !}

  ∧-nonzero : (p q : 𝕀) .{{_ : NonZero p}} .{{_ : NonZero q}} → NonZero (p ∧ q)
  ∧-nonzero = {!   !}

  ∧-nononeˡ : (p q : 𝕀) .{{_ : NonOne p}} → NonOne (p ∧ q)
  ∧-nononeˡ p q = {!   !}

  r : (p q : 𝕀) .{{_ : NonOne (p ∧ q)}} → 𝕀
  r p q {{h}} = _÷_ (p ∧ (1- q)) (1- (p ∧ q)) {{nonone-nonzero {p ∧ q} h}} {{!   !}}

  r/proof : (p q : 𝕀) .{{_ : NonOne (p ∧ q)}} → p ≡ (p ∧ q) ∨ (r p q)
  r/proof = {!   !}


  iterate : ℕ → 𝕀 → 𝕀
  iterate zero    p = 1𝕀
  iterate (suc n) p = p ∧ iterate n p

  flips : cmp (Π nat λ _ → F bool)
  flips zero    = ret true
  flips (suc n) = flip (F bool) ½ (ret false) (flips n)

  flips' : cmp (Π nat λ _ → F bool)
  flips' n = flip (F bool) (iterate n ½) (ret false) (ret true)

  proof : (n : ℕ) → flips n ≡ flips' n
  proof zero    = refl
  proof (suc n) =
    let open ≡-Reasoning in
    begin
      flips (suc n)
    ≡⟨⟩
      flip (F bool) ½ (ret false) (flips n)
    ≡⟨ Eq.cong (flip (F bool) ½ (ret false)) (proof n) ⟩
      flip (F bool) ½ (ret false) (flips' n)
    ≡⟨⟩
      flip (F bool) ½ (ret false) (flip (F bool) (iterate n ½) (ret false) (ret true))
    ≡⟨ flip/assocˡ (F bool) (ret false) (ret false) (ret true) {p = ½} {q = iterate n ½} (r/proof ½ (iterate n ½) {{∧-nononeˡ ½ (iterate n ½)}}) ⟩
      flip (F bool) (iterate (suc n) ½) (flip (F bool) (r ½ (iterate n ½) {{∧-nononeˡ ½ (iterate n ½)}}) (ret false) (ret false)) (ret true)
    ≡⟨⟩
      flip (F bool) (iterate (suc n) ½) (ret false) (ret true)
    ≡⟨⟩
      flips' (suc n)
    ∎


module MontyHall where
  costMonoid = ℤ-CostMonoid
  open CostMonoid costMonoid

  import Data.Integer as ℤ

  open import Calf costMonoid
  open import Calf.Probability costMonoid
  open import Calf.Types.Unit
  open import Calf.Types.Bool

  open import Relation.Nullary.Negation using (contradiction)
  open import Calf.Types.Product

  WIN LOSE : cmp (F unit)
  WIN = step (F unit) ℤ.-[1+ 999 ] (ret triv)
  LOSE = ret triv

  data Door : Set where
    d₁ d₂ d₃ : Door
  door = U (meta Door)

  _≡ᵇ_ : Door → Door → Bool
  d₁ ≡ᵇ d₁ = true
  d₁ ≡ᵇ d₂ = false
  d₁ ≡ᵇ d₃ = false
  d₂ ≡ᵇ d₁ = false
  d₂ ≡ᵇ d₂ = true
  d₂ ≡ᵇ d₃ = false
  d₃ ≡ᵇ d₁ = false
  d₃ ≡ᵇ d₂ = false
  d₃ ≡ᵇ d₃ = true

  uniform : cmp (F door)
  uniform = flip (F door) ⅓ (flip (F door) ½ (ret d₁) (ret d₂)) (ret d₃)

  -- Assume the prize is behind `d` and the guess was `d'`.
  -- Then, `monty d d'` gives a non-`d`, non-`d'` door with no prize.
  monty : cmp (Π door λ d → Π door λ d' →
    F (Σ++ door λ d'' → prod⁺ (U (meta (d ≢ d''))) (U (meta (d' ≢ d'')))))
  monty d₁ d₁ =
    flip (F (Σ++ door λ d'' → prod⁺ (U (meta (d₁ ≢ d''))) (U (meta (d₁ ≢ d''))))) ½
      (ret (d₂ , (λ ()) , λ ()))
      (ret (d₃ , (λ ()) , λ ()))
  monty d₁ d₂ = ret (d₃ , (λ ()) , λ ())
  monty d₁ d₃ = ret (d₂ , (λ ()) , λ ())
  monty d₂ d₁ = ret (d₃ , (λ ()) , λ ())
  monty d₂ d₂ =
    flip (F (Σ++ door λ d'' → prod⁺ (U (meta (d₂ ≢ d''))) (U (meta (d₂ ≢ d''))))) ½
      (ret (d₁ , (λ ()) , λ ()))
      (ret (d₃ , (λ ()) , λ ()))
  monty d₂ d₃ = ret (d₁ , (λ ()) , λ ())
  monty d₃ d₁ = ret (d₂ , (λ ()) , λ ())
  monty d₃ d₂ = ret (d₁ , (λ ()) , λ ())
  monty d₃ d₃ =
    flip (F (Σ++ door λ d'' → prod⁺ (U (meta (d₃ ≢ d''))) (U (meta (d₃ ≢ d''))))) ½
      (ret (d₁ , (λ ()) , λ ()))
      (ret (d₂ , (λ ()) , λ ()))

  play : (prize-door final-guess : Door) → cmp (F unit)
  play prize-door final-guess with prize-door ≡ᵇ final-guess
  ... | false = LOSE
  ... | true  = WIN

  stay : (d d' : Door) → d ≢ d' → Door
  stay d _ _ = d

  switch : (d d' : Door) → d ≢ d' → Door
  switch d₁ d₁ h = contradiction refl h
  switch d₁ d₂ h = d₃
  switch d₁ d₃ h = d₂
  switch d₂ d₁ h = d₃
  switch d₂ d₂ h = contradiction refl h
  switch d₂ d₃ h = d₁
  switch d₃ d₁ h = d₂
  switch d₃ d₂ h = d₁
  switch d₃ d₃ h = contradiction refl h

  game : Door → (strategy : (d d' : Door) → d ≢ d' → Door) → cmp (F unit)
  game prize-door strategy =
    bind (F unit) uniform λ guess →
    bind (F unit) (monty prize-door guess) λ (open-door , _ , guess≢open-door) →
    play prize-door (strategy guess open-door guess≢open-door)

  stay-bad : (prize-door : Door) → game prize-door stay ≡ flip (F unit) ⅓ LOSE WIN
  stay-bad d₁ =
    let open ≡-Reasoning in
    begin
      game d₁ stay
    ≡⟨⟩
      flip (F unit) ⅓ (flip (F unit) ½ WIN LOSE) LOSE
    ≡⟨ flip/assocʳ (F unit) WIN LOSE LOSE {p = ⅓} {q = ½} {r = ½} refl ⟩
      flip (F unit) ⅔ WIN (flip (F unit) ½ LOSE LOSE)
    ≡⟨⟩
      flip (F unit) ⅔ WIN LOSE
    ≡⟨ flip/sym (F unit) ⅔ WIN LOSE ⟩
      flip (F unit) ⅓ LOSE WIN
    ∎
  stay-bad d₂ =
    let open ≡-Reasoning in
    begin
      game d₂ stay
    ≡⟨⟩
      flip (F unit) ⅓ (flip (F unit) ½ LOSE WIN) LOSE
    ≡⟨ Eq.cong (λ e → flip (F unit) ⅓ e LOSE) (flip/sym (F unit) ½ LOSE WIN) ⟩
      flip (F unit) ⅓ (flip (F unit) ½ WIN LOSE) LOSE
    ≡⟨ flip/assocʳ (F unit) WIN LOSE LOSE {p = ⅓} {q = ½} {r = ½} refl ⟩
      flip (F unit) ⅔ WIN (flip (F unit) ½ LOSE LOSE)
    ≡⟨⟩
      flip (F unit) ⅔ WIN LOSE
    ≡⟨ flip/sym (F unit) ⅔ WIN LOSE ⟩
      flip (F unit) ⅓ LOSE WIN
    ∎
  stay-bad d₃ = refl

  switch-good : (prize-door : Door) → game prize-door switch ≡ flip (F unit) ⅓ WIN LOSE
  switch-good d₁ =
    let open ≡-Reasoning in
    begin
      game d₁ switch
    ≡⟨⟩
      flip (F unit) ⅓ (flip (F unit) ½ LOSE WIN) WIN
    ≡⟨ flip/assocʳ (F unit) LOSE WIN WIN {p = ⅓} {q = ½} {r = ½} refl ⟩
      flip (F unit) ⅔ LOSE (flip (F unit) ½ WIN WIN)
    ≡⟨⟩
      flip (F unit) ⅔ LOSE WIN
    ≡⟨ flip/sym (F unit) ⅔ LOSE WIN ⟩
      flip (F unit) ⅓ WIN LOSE
    ∎
  switch-good d₂ =
    let open ≡-Reasoning in
    begin
      game d₂ switch
    ≡⟨⟩
      flip (F unit) ⅓ (flip (F unit) ½ WIN LOSE) WIN
    ≡⟨ Eq.cong (λ e → flip (F unit) ⅓ e WIN) (flip/sym (F unit) ½ WIN LOSE) ⟩
      flip (F unit) ⅓ (flip (F unit) ½ LOSE WIN) WIN
    ≡⟨ flip/assocʳ (F unit) LOSE WIN WIN {p = ⅓} {q = ½} {r = ½} refl ⟩
      flip (F unit) ⅔ LOSE (flip (F unit) ½ WIN WIN)
    ≡⟨⟩
      flip (F unit) ⅔ LOSE WIN
    ≡⟨ flip/sym (F unit) ⅔ LOSE WIN ⟩
      flip (F unit) ⅓ WIN LOSE
    ∎
  switch-good d₃ = refl


module Expectation where
  costMonoid = ℚ-CostMonoid
  open CostMonoid costMonoid

  import Data.Integer as ℤ
  import Data.Rational as ℚ

  open import Calf costMonoid
  open import Calf.Probability costMonoid
  open import Calf.Types.Unit
  open import Calf.Types.Bool
  open import Calf.Types.Nat

  postulate
    expectation₁ : {X : tp neg} {c : cmp cost} {e₀ e₁ : cmp X} {p : 𝕀} →
      flip X p e₀ (step X c e₁) ≡ step X (toℚ p ℚ.* c) (flip X p e₀ e₁)

  expectation₀ : {X : tp neg} {c : cmp cost} {e₀ e₁ : cmp X} {p : 𝕀} →
    flip X p (step X c e₀) e₁ ≡ step X (toℚ (1- p) ℚ.* c) (flip X p e₀ e₁)
  expectation₀ {X} {c} {e₀} {e₁} {p} =
    let open ≡-Reasoning in
    begin
      flip X p (step X c e₀) e₁
    ≡⟨ flip/sym X p (step X c e₀) e₁ ⟩
      flip X (1- p) e₁ (step X c e₀)
    ≡⟨ expectation₁ {X = X} {c = c} {e₀ = e₁} {e₁ = e₀} {p = 1- p} ⟩
      step X (toℚ (1- p) ℚ.* c) (flip X (1- p) e₁ e₀)
    ≡˘⟨ Eq.cong (step X (toℚ (1- p) ℚ.* c)) (flip/sym X p e₀ e₁) ⟩
      step X (toℚ (1- p) ℚ.* c) (flip X p e₀ e₁)
    ∎

  foo : cmp (F unit)
  foo =
    flip (F unit) ⅓
      (step (F unit) (ℤ.+ 10 ℚ./ 1) (ret triv))
      (step (F unit) (ℤ.+ 20 ℚ./ 1) (ret triv))

  bar : cmp (F unit)
  bar = step (F unit) (ℤ.+ 40 ℚ./ 3) (ret triv)

  foo≡bar : foo ≡ bar
  foo≡bar =
    let open ≡-Reasoning in
    begin
      flip (F unit) ⅓
        (step (F unit) (ℤ.+ 10 ℚ./ 1) (ret triv))
        (step (F unit) (ℤ.+ 20 ℚ./ 1) (ret triv))
    ≡⟨ expectation₀ {X = F unit} {c = ℤ.+ 10 ℚ./ 1} {e₀ = ret triv} {e₁ = step (F unit) (ℤ.+ 20 ℚ./ 1) (ret triv)} {p = ⅓} ⟩
      ( step (F unit) (ℤ.+ 20 ℚ./ 3) $
        flip (F unit) ⅓
          (ret triv)
          (step (F unit) (ℤ.+ 20 ℚ./ 1) (ret triv))
      )
    ≡⟨ Eq.cong (step (F unit) (ℤ.+ 20 ℚ./ 3)) (expectation₁ {X = F unit} {c = ℤ.+ 20 ℚ./ 1} {e₀ = ret triv} {e₁ = ret triv} {p = ⅓}) ⟩
      ( step (F unit) (ℤ.+ 20 ℚ./ 3) $
        step (F unit) (ℤ.+ 20 ℚ./ 3) $
        flip (F unit) ⅓ (ret triv) (ret triv)
      )
    ≡⟨⟩
      ( step (F unit) (ℤ.+ 40 ℚ./ 3) $
        flip (F unit) ⅓ (ret triv) (ret triv)
      )
    ≡⟨⟩
      step (F unit) (ℤ.+ 40 ℚ./ 3) (ret triv)
    ∎
