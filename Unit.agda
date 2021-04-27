{-# OPTIONS --prop --rewriting #-}
open import Prelude
open import Metalanguage

postulate
  unit : tp pos
  triv : val unit
  unit/eta : ∀ {u v : val unit} → u ≡ v