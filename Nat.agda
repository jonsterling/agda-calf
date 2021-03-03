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