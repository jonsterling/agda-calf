{-# OPTIONS --cubical-compatible --safe #-}

module CalfMonad.Util where

open import Agda.Builtin.Nat
open import Data.Fin.Base                              using (Fin; suc; zero)
open import Data.Product                               using (_×_; _,_)
open import Data.Unit.Polymorphic.Base                 using (⊤)
open import Data.Vec.Relation.Unary.All                using (_∷_)
open import Data.Vec.Relation.Unary.All.Properties     using (tabulate⁺)
open import Relation.Binary.PropositionalEquality.Core using (module ≡-Reasoning; _≡_; cong; cong₂; refl)

import CalfMonad.CostMonad as CalfMonad
import CalfMonad.Monad     as CalfMonad
open import CalfMonad.CostMonoid

open ≡-Reasoning

tabulate⁺-cong : ∀ {a A p P n f Pf Pf′} → (∀ i → Pf i ≡ Pf′ i) → tabulate⁺ {a} {A} {p} {P} {n} {f} Pf ≡ tabulate⁺ {a} {A} {p} {P} {n} {f} Pf′
tabulate⁺-cong {n = zero} eq = refl
tabulate⁺-cong {n = suc n} eq = cong₂ _∷_ (eq zero) (tabulate⁺-cong λ i → eq (suc i))

Prod : ∀ {n a} (As : Fin n → Set a) → Set a
Prod {zero} As = ⊤
Prod {suc n} As = As zero × Prod λ i → As (suc i)

module Prod where
  tabulate : ∀ {n a As} (xs : ∀ i → As i) → Prod {n} {a} As
  tabulate {zero} xs = _
  tabulate {suc n} xs = xs zero , tabulate λ i → xs (suc i)

  lookup : ∀ {n a As} → Prod {n} {a} As → ∀ i → As i
  lookup (x , xs) zero = x
  lookup (x , xs) (suc i) = lookup xs i

  foldr : ∀ {n a As b} {B : Set b} → (∀ {i} → As i → B → B) → B → Prod {n} {a} As → B
  foldr {zero} f y _ = y
  foldr {suc n} f y (x , xs) = f x (foldr f y xs)

  map : ∀ {n a As b Bs} → (∀ {i} → As i → Bs i) → Prod {n} {a} As → Prod {n} {b} Bs
  map {zero} f _ = _
  map {suc n} f (x , xs) = f x , map f xs

  zipWith : ∀ {n a As b Bs c Cs} → (∀ {i} → As i → Bs i → Cs i) → Prod {n} {a} As → Prod {n} {b} Bs → Prod {n} {c} Cs
  zipWith {zero} f _ _ = _
  zipWith {suc n} f (x , xs) (y , ys) = f x y , zipWith f xs ys

  tabulate-cong : ∀ {n a As xs xs′} → (∀ i → xs i ≡ xs′ i) → tabulate {n} {a} {As} xs ≡ tabulate {n} {a} {As} xs′
  tabulate-cong {zero} eq = refl
  tabulate-cong {suc n} eq = cong₂ _,_ (eq zero) (tabulate-cong λ i → eq (suc i))

  lookup-tabulate : ∀ {n a As} xs i → lookup (tabulate {n} {a} {As} xs) i ≡ xs i
  lookup-tabulate xs zero = refl
  lookup-tabulate xs (suc i) = lookup-tabulate _ i

  tabulate-lookup : ∀ {n a As} xs → tabulate (lookup {n} {a} {As} xs) ≡ xs
  tabulate-lookup {zero} _ = refl
  tabulate-lookup {suc n} (x , xs) = cong (x ,_) (tabulate-lookup xs)

  map-tabulate : ∀ {n a As b Bs} (f : ∀ {i} → As i → Bs i) xs → map {n} {a} {As} {b} {Bs} f (tabulate xs) ≡ tabulate λ i → f (xs i)
  map-tabulate {zero} f xs = refl
  map-tabulate {suc n} f xs = cong (_ ,_) (map-tabulate _ _)

module Monad {ℓ ℓ′ M} (monad : CalfMonad.Monad {ℓ} {ℓ′} M) where
  open CalfMonad.Monad monad

  seq : ∀ {n As} → Prod (λ i → M (As i)) → M (Prod {n} As)
  seq {zero} _ = pure _
  seq {suc n} (e , es) = do
    x ← e
    xs ← seq es
    pure (x , xs)

  pure-seq : ∀ {n As} as → seq {n} {As} (Prod.map pure as) ≡ pure as
  pure-seq {zero} _ = begin
    pure _ ∎
  pure-seq {suc n} (a , as) = begin
    pure a >>= (λ a → seq (Prod.map pure as) >>= λ as → pure (a , as)) ≡⟨ pure->>= a _ ⟩
    seq (Prod.map pure as) >>= (λ as → pure (a , as))                  ≡⟨ cong (_>>= _) (pure-seq as) ⟩
    pure as >>= (λ as → pure (a , as))                                 ≡⟨ pure->>= as _ ⟩
    pure (a , as)                                                      ∎

module CostMonad {ℓ ℓ′ ℓ″ M ℂ monad costMonoid} (costMonad : CalfMonad.CostMonad {ℓ} {ℓ′} {ℓ″} {M} {ℂ} monad costMonoid) where
  open CalfMonad.Monad monad
  open CostMonoid costMonoid
  open CalfMonad.CostMonad costMonad

  open Monad monad public

  step-pure-seq : ∀ {n As} ps as → seq {n} {As} (Prod.zipWith (λ p a → step p >> pure a) ps as) ≡ step (Prod.foldr _⊕_ 𝟘 ps) >> pure as
  step-pure-seq {zero} _ _ = begin
    pure _           ≡˘⟨ step-𝟘->> _ ⟩
    step 𝟘 >> pure _ ∎
  step-pure-seq {suc n} (p , ps) (a , as) = begin
    (step p >> pure a) >>= (λ a → seq (Prod.zipWith (λ p a → step p >> pure a) ps as) >>= λ as → pure (a , as)) ≡⟨ >>=->>= _ _ _ ⟩
    step p >> (pure a >>= λ a → seq (Prod.zipWith (λ p a → step p >> pure a) ps as) >>= λ as → pure (a , as))   ≡⟨ cong (_ >>_) (pure->>= a _) ⟩
    step p >> (seq (Prod.zipWith (λ p a → step p >> pure a) ps as) >>= λ as → pure (a , as))                    ≡⟨ cong (λ e → _ >> (e >>= _)) (step-pure-seq ps as) ⟩
    step p >> ((step (Prod.foldr _⊕_ 𝟘 ps) >> pure as) >>= λ as → pure (a , as))                                ≡⟨ cong (_ >>_) (>>=->>= _ _ _) ⟩
    step p >> (step (Prod.foldr _⊕_ 𝟘 ps) >> (pure as >>= λ as → pure (a , as)))                                ≡⟨ cong (λ e → _ >> (_ >> e)) (pure->>= as _) ⟩
    step p >> (step (Prod.foldr _⊕_ 𝟘 ps) >> pure (a , as))                                                     ≡˘⟨ >>=->>= _ _ _ ⟩
    (step p >> step (Prod.foldr _⊕_ 𝟘 ps)) >> pure (a , as)                                                     ≡˘⟨ cong (_>> _) (step-⊕ p _) ⟩
    step (p ⊕ Prod.foldr _⊕_ 𝟘 ps) >> pure (a , as)                                                             ∎

module ParCostMonad {ℓ ℓ′ ℓ″ M ℂ monad costMonoid costMonad parCostMonoid} (parCostMonad : CalfMonad.ParCostMonad {ℓ} {ℓ′} {ℓ″} {M} {ℂ} {monad} {costMonoid} costMonad parCostMonoid) where
  open CalfMonad.Monad monad
  open CostMonoid costMonoid
  open CalfMonad.CostMonad costMonad
  open ParCostMonoid parCostMonoid
  open CalfMonad.ParCostMonad parCostMonad

  open CostMonad costMonad public

  par : ∀ {n As} → Prod (λ i → M (As i)) → M (Prod {n} As)
  par {zero} _ = pure _
  par {suc n} (e , es) = e & par es

  step-pure-par : ∀ {n As} ps as → par {n} {As} (Prod.zipWith (λ p a → step p >> pure a) ps as) ≡ step (Prod.foldr _⊗_ 𝟘 ps) >> pure as
  step-pure-par {zero} _ _ = begin
    pure _           ≡˘⟨ step-𝟘->> _ ⟩
    step 𝟘 >> pure _ ∎
  step-pure-par {suc n} (p , ps) (a , as) = begin
    (step p >> pure a) & par (Prod.zipWith (λ p a → step p >> pure a) ps as) ≡⟨ cong (_ &_) (step-pure-par ps as) ⟩
    (step p >> pure a) & (step (Prod.foldr _⊗_ 𝟘 ps) >> pure as)             ≡⟨ step-pure-&-step-pure p _ a as ⟩
    step (p ⊗ Prod.foldr _⊗_ 𝟘 ps) >> pure (a , as)                          ∎
