{-# OPTIONS --prop --rewriting #-}
open import Prelude
open import Metalanguage

open import Data.Unit public using (⊤) renaming (tt to triv)

postulate
  unit : tp pos
  unit/decode : val unit ≡ ⊤
  {-# REWRITE unit/decode #-}
