{-# OPTIONS --prop --without-K --rewriting #-}
open import Prelude
open import Metalanguage

open import Data.Sum public

postulate
  sum : tp pos → tp pos → tp pos
  sum/decode : ∀ {A B} → val (sum A B) ≡ _⊎_ (val A) (val B)
  {-# REWRITE sum/decode #-}

sum/case : ∀ A B (X : val (sum A B) → tp neg) → (s : val (sum A B)) → ((a : val A) → cmp (X (inj₁ a))) → ((b : val B) → cmp (X (inj₂ b))) → cmp (X s)
sum/case A B X (inj₁ x) b₁ _  = b₁ x
sum/case A B X (inj₂ x) _  b₂ = b₂ x
