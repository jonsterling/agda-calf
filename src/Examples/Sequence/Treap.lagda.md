# Treap

In this file, we implement and verify the [treap](https://en.wikipedia.org/wiki/Treap) data structure.

<!--
```agda
{-# OPTIONS --prop --rewriting #-}
```
-->

```agda
module Examples.Sequence.Treap where

open import Algebra.Cost

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid

open import Calf costMonoid
```
