{-# OPTIONS --prop --rewriting #-}

module Examples.Exp2 where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Bool

monoidOn = Monoid.monoidOn (OrderedMonoid.monoid ⊕-orderedMonoid)
import Calf.Upper ⊕-orderedMonoid monoidOn as ⊕U
import Calf.Upper ⊗-orderedMonoid monoidOn as ⊗U

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)
open import Data.Nat as Nat
open import Data.Nat.Properties as N using (module ≤-Reasoning)
open import Data.Product
open import Data.Empty

Correct : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ))) → Set
Correct exp₂ = (n : ℕ) → ◯ (exp₂ n ≡ ret (2 ^ n))

lemma/2^suc : ∀ n → 2 ^ n + 2 ^ n ≡ 2 ^ suc n
lemma/2^suc n =
  begin
    2 ^ n + 2 ^ n
  ≡˘⟨ Eq.cong ((2 ^ n) +_) (N.*-identityˡ (2 ^ n)) ⟩
    2 ^ n + (2 ^ n + 0)
  ≡⟨⟩
    2 ^ n + (2 ^ n + 0 * (2 ^ n))
  ≡⟨⟩
    2 * (2 ^ n)
  ≡⟨⟩
    2 ^ suc n
  ∎
    where open ≡-Reasoning

lemma/2^n≢0 : ∀ n → 2 ^ n ≢ zero
lemma/2^n≢0 n 2^n≡0 with N.m^n≡0⇒m≡0 2 n 2^n≡0
... | ()

lemma/pred-+ : ∀ m n → m ≢ zero → pred m + n ≡ pred (m + n)
lemma/pred-+ zero    n m≢zero = ⊥-elim (m≢zero refl)
lemma/pred-+ (suc m) n m≢zero = refl

module Slow where
  exp₂ : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
  exp₂ zero = ret (suc zero)
  exp₂ (suc n) =
    bind (F (U (meta ℕ))) (exp₂ n & exp₂ n) λ (r₁ , r₂) →
      step' (F (U (meta ℕ))) (1 , 1) (ret (r₁ + r₂))

  exp₂/correct : Correct exp₂
  exp₂/correct zero    u = refl
  exp₂/correct (suc n) u =
    begin
      exp₂ (suc n)
    ≡⟨⟩
      (bind (F (U (meta ℕ))) (exp₂ n & exp₂ n) λ (r₁ , r₂) →
        step' (F (U (meta ℕ))) (1 , 1) (ret (r₁ + r₂)))
    ≡⟨ Eq.cong (bind (F (U (meta ℕ))) (exp₂ n & exp₂ n)) (funext (λ (r₁ , r₂) → step'/ext (F (U (meta ℕ))) _ (1 , 1) u)) ⟩
      (bind (F (U (meta ℕ))) (exp₂ n & exp₂ n) λ (r₁ , r₂) →
        ret (r₁ + r₂))
    ≡⟨ Eq.cong (λ e → bind (F (U (meta ℕ))) (e & e) _) (exp₂/correct n u) ⟩
      (bind (F (U (meta ℕ))) (ret {U (meta ℕ)} (2 ^ n) & ret {U (meta ℕ)} (2 ^ n)) λ (r₁ , r₂) →
        ret (r₁ + r₂))
    ≡⟨ bind/par {p₁ = 𝟘} {p₂ = 𝟘} ⟩
      step' (F (U (meta ℕ))) (𝟘 ⊗ 𝟘) (ret (2 ^ n + 2 ^ n))
    ≡⟨⟩
      ret (2 ^ n + 2 ^ n)
    ≡⟨ Eq.cong ret (lemma/2^suc n) ⟩
      ret (2 ^ suc n)
    ∎
      where open ≡-Reasoning

  exp₂/cost : cmp (Π (U (meta ℕ)) λ _ → cost)
  exp₂/cost n = pred (2 ^ n) , n

  exp₂≤exp₂/cost/seq : ∀ n → ⊕U.ub (U (meta ℕ)) (exp₂ n) (exp₂/cost n)
  exp₂≤exp₂/cost/seq zero    = ub/ret
  exp₂≤exp₂/cost/seq (suc n) with exp₂≤exp₂/cost/seq n
  ... | ⊕U.ub/intro {q = (w , s)} _ ih h-eq rewrite eq/ref h-eq =
    ⊕U.ub/relax
      (begin
        proj₁ ((w , s) ⊗ (w , s) ⊕ (1 , 1) ⊕ 𝟘)
      ≡⟨⟩
        proj₁ ((w + w + 1 , s ⊔ s + 1) ⊕ 𝟘)
      ≡⟨ Eq.cong proj₁ (CostMonoid.identityʳ costMonoid (w + w + 1 , s ⊔ s + 1)) ⟩
        w + w + 1
      ≡⟨ N.+-comm (w + w) 1 ⟩
        suc (w + w)
      ≤⟨ s≤s (N.+-mono-≤ ih ih) ⟩
        suc (pred (2 ^ n) + pred (2 ^ n))
      ≡˘⟨ N.+-suc (pred (2 ^ n)) (pred (2 ^ n)) ⟩
        pred (2 ^ n) + suc (pred (2 ^ n))
      ≡⟨ Eq.cong (pred (2 ^ n) +_) (N.suc[pred[n]]≡n (lemma/2^n≢0 n)) ⟩
        pred (2 ^ n) + 2 ^ n
      ≡⟨ lemma/pred-+ (2 ^ n) (2 ^ n) (lemma/2^n≢0 n) ⟩
        pred (2 ^ n + 2 ^ n)
      ≡⟨ Eq.cong pred (lemma/2^suc n) ⟩
        pred (2 ^ suc n)
      ∎)
      (ub/step ((w , s) ⊗ (w , s) ⊕ (1 , 1)) 𝟘 ub/ret)
      where open ≤-Reasoning

  exp₂≤exp₂/cost/par : ∀ n → ⊗U.ub (U (meta ℕ)) (exp₂ n) (exp₂/cost n)
  exp₂≤exp₂/cost/par zero    = ⊗U.ub/intro {q = 𝟘} 1 (≤ₓ-refl {𝟘}) (ret (eq/intro refl))
  exp₂≤exp₂/cost/par (suc n) with exp₂≤exp₂/cost/par n
  ... | ⊗U.ub/intro {q = (w , s)} a ih h-eq rewrite eq/ref h-eq =
    ⊗U.ub/intro {q = (w , s) ⊗ (w , s) ⊕ (1 , 1)} (a + a)
      (begin
        proj₂ ((w , s) ⊗ (w , s) ⊕ (1 , 1))
      ≡⟨⟩
        s ⊔ s + 1
      ≡⟨ N.+-comm (s ⊔ s) 1 ⟩
        suc (s ⊔ s)
      ≡⟨ Eq.cong suc (N.⊔-idem s) ⟩
        suc s
      ≤⟨ s≤s ih ⟩
        suc n
      ∎)
      (ret (eq/intro refl))
      where open ≤-Reasoning

module Fast where

  exp₂ : cmp (Π (U (meta ℕ)) λ _ → F (U (meta ℕ)))
  exp₂ zero = ret (suc zero)
  exp₂ (suc n) =
    bind (F (U (meta ℕ))) (exp₂ n) λ r →
      step' (F (U (meta ℕ))) (1 , 1) (ret (r + r))

  exp₂/correct : Correct exp₂
  exp₂/correct zero    u = refl
  exp₂/correct (suc n) u =
    begin
      exp₂ (suc n)
    ≡⟨⟩
      (bind (F (U (meta ℕ))) (exp₂ n) λ r →
        step' (F (U (meta ℕ))) (1 , 1) (ret (r + r)))
    ≡⟨ Eq.cong (bind (F (U (meta ℕ))) (exp₂ n)) (funext (λ r → step'/ext (F (U (meta ℕ))) _ (1 , 1) u)) ⟩
      (bind (F (U (meta ℕ))) (exp₂ n) λ r →
        ret (r + r))
    ≡⟨ Eq.cong (λ e → bind (F (U (meta ℕ))) e _) (exp₂/correct n u) ⟩
      (bind (F (U (meta ℕ))) (ret {U (meta ℕ)} (2 ^ n)) λ r →
        ret (r + r))
    ≡⟨⟩
      ret (2 ^ n + 2 ^ n)
    ≡⟨ Eq.cong ret (lemma/2^suc n) ⟩
      ret (2 ^ suc n)
    ∎
      where open ≡-Reasoning

  exp₂/cost : cmp (Π (U (meta ℕ)) λ _ → cost)
  exp₂/cost n = n , n

  exp₂≤exp₂/cost/seq : ∀ n → ⊕U.ub (U (meta ℕ)) (exp₂ n) (exp₂/cost n)
  exp₂≤exp₂/cost/seq zero    = ub/ret
  exp₂≤exp₂/cost/seq (suc n) with exp₂≤exp₂/cost/seq n
  ... | ⊕U.ub/intro {q = (w , s)} _ ih h-eq rewrite eq/ref h-eq =
    ⊕U.ub/relax
      (begin
        proj₁ ((w , s) ⊕ (1 , 1) ⊕ 𝟘)
      ≡⟨⟩
        proj₁ ((w + 1 , s + 1) ⊕ 𝟘)
      ≡⟨ Eq.cong proj₁ (CostMonoid.identityʳ costMonoid (w + 1 , s + 1)) ⟩
        w + 1
      ≡⟨ N.+-comm w 1 ⟩
        suc w
      ≤⟨ s≤s ih ⟩
        suc n
      ∎)
      (ub/step ((w , s) ⊕ (1 , 1)) 𝟘 ub/ret)
      where open ≤-Reasoning

  exp₂≤exp₂/cost/par : ∀ n → ⊗U.ub (U (meta ℕ)) (exp₂ n) (exp₂/cost n)
  exp₂≤exp₂/cost/par zero    = ⊗U.ub/intro {q = 𝟘} 1 (≤ₓ-refl {𝟘}) (ret (eq/intro refl))
  exp₂≤exp₂/cost/par (suc n) with exp₂≤exp₂/cost/par n
  ... | ⊗U.ub/intro {q = (w , s)} a ih h-eq rewrite eq/ref h-eq =
    ⊗U.ub/intro {q = (w , s) ⊕ (1 , 1)} (a + a)
      (begin
        proj₂ ((w , s) ⊕ (1 , 1))
      ≡⟨⟩
        s + 1
      ≡⟨ N.+-comm s 1 ⟩
        suc s
      ≤⟨ s≤s ih ⟩
        suc n
      ∎)
      (ret (eq/intro refl))
      where open ≤-Reasoning

slow≡fast : ◯ (Slow.exp₂ ≡ Fast.exp₂)
slow≡fast u = funext λ n →
  begin
    Slow.exp₂ n
  ≡⟨ Slow.exp₂/correct n u ⟩
    ret (2 ^ n)
  ≡˘⟨ Fast.exp₂/correct n u ⟩
    Fast.exp₂ n
  ∎
    where open ≡-Reasoning
