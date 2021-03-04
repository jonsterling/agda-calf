{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import Thunkable
open import Univ

postulate
  nat : tp pos 
  zero : val nat 
  suc : val nat → val nat
  rec : (n : val nat) → (X : val nat → tp neg) → 
    cmp (X zero) → 
    ((n : val nat) → val (U (X n)) → cmp (X (suc n))) → 
    cmp (X n)
  rec/beta/zero : (X : val nat → tp neg) → 
    (e0 : cmp (X zero)) → 
    (e1 : (n : val nat) → val (U (X n)) → cmp (X (suc n))) → 
    rec zero X e0 e1 ≡ e0
  {-# REWRITE rec/beta/zero #-}
  rec/beta/suc : (n : val nat) → (X : val nat → tp neg) → 
    (e0 : cmp (X zero)) → 
    (e1 : (n : val nat) → val (U (X n)) → cmp (X (suc n))) → 
    rec (suc n) X e0 e1 ≡ e1 n (rec n X e0 e1)
  {-# REWRITE rec/beta/suc #-}

postulate
  th/rec : ∀ (n : val nat) → 
    (X : val nat → tp pos)
    (ez : cmp (F (X zero))) → 
    (es : (n : val nat) → val (U (F (X n))) → cmp (F (X (suc n)))) →
    th (F (X zero)) ez → 
    ((n : val nat) → (r : val (U (F (X n)))) → th (F (X n)) r → th (F (X (suc n))) (es n r)) → 
    th (F (X n)) (rec n (λ n → F (X n)) ez es)

postulate
  nat/code : val (univ pos 0) 
  nat/decode : el⁺ 0 nat/code ≡ nat
  {-# REWRITE nat/decode #-}