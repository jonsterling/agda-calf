{-# OPTIONS --prop --rewriting #-}
open import Prelude
open import Metalanguage

postulate
  void : tp pos
  abort : ∀ {C} → val void → cmp C
