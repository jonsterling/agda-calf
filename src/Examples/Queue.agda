module Examples.Queue where

import Cubical.Data.List.Properties as List
import Cubical.Data.Nat.Properties as Nat

open import Calf.Core.Abstract
open import Calf.Core.Cost
open import Calf.Value hiding (empty)
open import Calf.Value.List
open import Calf.Value.Nat
open import Calf.Computation
open import Calf.Computation.Abstraction
open import Calf.Computation.Copower
open import Calf.Computation.Free


record PreQueue : 𝒱₁ where
  field
    Q : 𝒞
    empty : U Q
    enqueue : ℕ → Q ⊸ Q
    dequeue : Q ⊸ ℕₚ ⋊ Q
open PreQueue

LQ : 𝒞
LQ = F (List ℕ)

emptyᴸ : U LQ
emptyᴸ = ret []

enqueueᴸ : ℕ → LQ ⊸ LQ
enqueueᴸ e = F-rec λ l → LQ .charge 1 (ret (l ++ [ e ]))

dequeueᴸ : LQ ⊸ ℕₚ ⋊ LQ
dequeueᴸ = F-rec λ
  { []      → 0 , ret []
  ; (x ∷ l) → x , ret l }

list-prequeue : PreQueue
list-prequeue .Q = LQ
list-prequeue .empty = emptyᴸ
list-prequeue .enqueue = enqueueᴸ
list-prequeue .dequeue = dequeueᴸ

BQ : 𝒞
BQ = F (List ℕ × List ℕ)

emptyᴮ : U BQ
emptyᴮ = ret ([] , [])

enqueueᴮ : ℕ → BQ ⊸ BQ
enqueueᴮ e = F-rec λ (back , front) → ret (e ∷ back , front)

reverse-front : List ℕ → U (ℕₚ ⋊ BQ)
reverse-front back with reverse back
... | []    = 0 , BQ .charge (# length back) (ret ([] , []))
... | x ∷ l = x , BQ .charge (# length back) (ret ([] , l))

dequeueᴮ : BQ ⊸ (ℕₚ ⋊ BQ)
dequeueᴮ = F-rec λ
  { (back , x ∷ front) → x , ret (back , front)
  ; (back , [])        → reverse-front back }

batched-prequeue : PreQueue
batched-prequeue .Q = BQ
batched-prequeue .empty = emptyᴮ
batched-prequeue .enqueue = enqueueᴮ
batched-prequeue .dequeue = dequeueᴮ


record Queue : 𝒱₁ where
  field
    prequeue : PreQueue
    spec : ⟨ ABS ⟩ → prequeue ≡ list-prequeue
open Queue

α : BQ ⊸ LQ
α = F-rec λ (l₁ , l₂) → LQ .charge (# length l₁) (ret (l₂ ++ reverse l₁))


opaque
  unfolding ℂ

  empty-coherent : α .U emptyᴮ ≡ emptyᴸ
  empty-coherent = F-rec-β ∙ F _ .charge-0

  enqueue-coherent :
    (e : ℕ) (q : U BQ)
    → α .U (enqueueᴮ e .U q) ≡ enqueueᴸ e .U (α .U q)
  enqueue-coherent e q =
    cong (λ h → h .U q)
      ( costed-map (λ (back , front) → e ∷ back , front) _ _
      ∙ costed-cong
          (λ (back , front) → sym (List.++-assoc front (reverse back) [ e ]))
          (λ (back , _) → cong ℕ→ℂ (Nat.+-comm 1 (length back)) ∙ ℕ→ℂ-+ (length back) 1)
      ∙ sym (costed-⨾ᶜ _ _ _ _))

module Dequeue where
  BLQ = Abstractionᶜ BQ LQ α

  opaque
    unfolding ℂ

    dequeue-coherent :
      (q : U BQ) → ⋊-map ℕₚ α .U (dequeueᴮ .U q) ≡ dequeueᴸ .U (α .U q)
    dequeue-coherent q =
      cong (λ f → f .U q)
        (F-rec-path
          (dequeueᴮ ⨾ᶜ ⋊-map ℕₚ α)
          (α ⨾ᶜ dequeueᴸ)
          (funExt dequeue-lemma))
      where
        dequeue-lemma : (x : List ℕ × List ℕ)
          → (dequeueᴮ ⨾ᶜ ⋊-map ℕₚ α) .U (ret x) ≡ (α ⨾ᶜ dequeueᴸ) .U (ret x)
        dequeue-lemma (back , x ∷ front) =
            dequeueᴮ .U (ret (back , x ∷ front)) .proj₁ ,
            α .U (dequeueᴮ .U (ret (back , x ∷ front)) .proj₂)
          ≡⟨ cong (λ e → e .proj₁ , α .U (e .proj₂)) F-rec-β ⟩
            x , α .U (ret (back , front))
          ≡⟨ cong (x ,_) F-rec-β ⟩
            x , LQ .charge (# length back) (ret (front ++ reverse back))
          ≡⟨ refl ⟩
            (ℕₚ ⋊ LQ) .charge (# length back) (x , ret (front ++ reverse back))
          ≡⟨ sym (cong ((ℕₚ ⋊ LQ) .charge (# length back)) F-rec-β) ⟩
            (ℕₚ ⋊ LQ) .charge (# length back) (dequeueᴸ .U (ret (x ∷ front ++ reverse back)))
          ≡⟨ sym (dequeueᴸ .charge (# length back) (ret _)) ⟩
            dequeueᴸ .U (LQ .charge (# length back) (ret ((x ∷ front) ++ reverse back)))
          ≡⟨ sym (cong (dequeueᴸ .U) F-rec-β) ⟩
            dequeueᴸ .U (α .U (ret (back , x ∷ front)))
          ∎
        dequeue-lemma (back , []) =
            dequeueᴮ .U (ret (back , [])) .proj₁ ,
            α .U (dequeueᴮ .U (ret (back , [])) .proj₂)
          ≡⟨ cong (λ e → e .proj₁ , α .U (e .proj₂)) F-rec-β ⟩
            reverse-front back .proj₁ , α .U (reverse-front back .proj₂)
          ≡⟨ lemma ⟩
            dequeueᴸ .U (LQ .charge (# length back) (ret (reverse back)))
          ≡⟨ sym (cong (dequeueᴸ .U) F-rec-β) ⟩
            dequeueᴸ .U (α .U (ret (back , [])))
          ∎
          where
            lemma :
              (reverse-front back .proj₁ , α .U (reverse-front back .proj₂))
              ≡ dequeueᴸ .U (LQ .charge (# length back) (ret (reverse back)))
            lemma with reverse back
            ... | [] =
                0 , α .U (BQ .charge (# length back) (ret ([] , [])))
              ≡⟨ cong (0 ,_) (α .charge (# length back) _) ⟩
                0 , F _ .charge (# length back) (α .U (ret ([] , [])))
              ≡⟨ cong (λ e → 0 , F _ .charge (# length back) e) F-rec-β ⟩
                0 , F _ .charge (# length back) (LQ .charge 0 (ret []))
              ≡⟨ cong (λ e → 0 , F _ .charge (# length back) e) (LQ .charge-0) ⟩
                (ℕₚ ⋊ LQ) .charge (# length back) (0 , ret [])
              ≡⟨ sym (cong ((ℕₚ ⋊ LQ) .charge (# length back)) F-rec-β) ⟩
                (ℕₚ ⋊ LQ) .charge (# length back) (dequeueᴸ .U (ret []))
              ≡⟨ sym (dequeueᴸ .charge (# length back) _) ⟩
                dequeueᴸ .U (LQ .charge (# length back) (ret []))
              ∎
            ... | x ∷ front =
                x , α .U (BQ .charge (# length back) (ret ([] , front)))
              ≡⟨ cong (x ,_) (α .charge (# length back) _) ⟩
                x , F _ .charge (# length back) (α .U (ret ([] , front)))
              ≡⟨ cong (λ e → x , F _ .charge (# length back) e) F-rec-β ⟩
                x , F _ .charge (# length back) (LQ .charge 0 (ret (front ++ [])))
              ≡⟨ cong (λ e → x , F _ .charge (# length back) e) (LQ .charge-0) ⟩
                x , F _ .charge (# length back) (ret (front ++ []))
              ≡⟨ cong (λ l → x , F _ .charge (# length back) (ret l)) (List.++-unit-r front) ⟩
                x , F _ .charge (# length back) (ret front)
              ≡⟨ refl ⟩
                (ℕₚ ⋊ LQ) .charge (# length back) (x , ret front)
              ≡⟨ sym (cong ((ℕₚ ⋊ LQ) .charge (# length back)) F-rec-β) ⟩
                (ℕₚ ⋊ LQ) .charge (# length back) (dequeueᴸ .U (ret (x ∷ front)))
              ≡⟨ sym (dequeueᴸ .charge (# length back) _) ⟩
                dequeueᴸ .U (LQ .charge (# length back) (ret (x ∷ front)))
              ∎


  dequeueᴬ : BLQ ⊸ ℕₚ ⋊ BLQ
  dequeueᴬ = squareᶜ α (⋊-map ℕₚ α) dequeueᴮ dequeueᴸ dequeue-coherent ⨾ᶜ ⋊-Abstractionᶜ ℕₚ α


batched-queue : Queue
batched-queue .prequeue .Q = Abstractionᶜ BQ LQ α
batched-queue .prequeue .empty = triangle-U α emptyᴮ emptyᴸ empty-coherent
batched-queue .prequeue .enqueue e = squareᶜ α α (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e)
batched-queue .prequeue .dequeue = Dequeue.dequeueᴬ
batched-queue .spec abs i .Q = Abstractionᶜ-open α abs i
batched-queue .spec abs i .empty =
  triangle-U-openP α emptyᴮ emptyᴸ empty-coherent abs i
batched-queue .spec abs i .enqueue e =
  square-openP α α (enqueueᴮ e) (enqueueᴸ e) (enqueue-coherent e) abs i
batched-queue .spec abs i .dequeue =
  ( (λ i →
      square-openP α (⋊-map ℕₚ α) dequeueᴮ dequeueᴸ Dequeue.dequeue-coherent abs i
        ⨾ᶜ ⋊-Abstractionᶜ-openP ℕₚ α abs i)
  ▷ ⨾ᶜ-identityʳ dequeueᴸ) i
