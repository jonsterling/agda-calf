{-# OPTIONS --prop --rewriting #-}
open import Prelude
open import Metalanguage

postulate
  sum : tp pos → tp pos → tp pos
  inl : ∀ {A B} → val A → val (sum A B)
  inr : ∀ {A B} → val B → val (sum A B)
  sum/case : ∀ A B (X : val (sum A B) → tp neg) → (s : val (sum A B)) → ((a : val A) → cmp (X (inl a))) → ((b : val B) → cmp (X (inr b))) → cmp (X s)
  case/inl : ∀ {A B X} → (a : val A) → (e1 : (a : val A) → cmp (X (inl a))) → (e2 : (b : val B) → cmp (X (inr b))) →
      sum/case A B X (inl a) e1 e2 ≡ e1 a
  {-# REWRITE case/inl #-}
  case/inr : ∀ {A B X} → (b : val B) → (e1 : (a : val A) → cmp (X (inl a))) → (e2 : (b : val B) → cmp (X (inr b))) →
      sum/case A B X (inr b) e1 e2 ≡ e2 b
  {-# REWRITE case/inr #-}