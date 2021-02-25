{-# OPTIONS --prop --rewriting #-}

module cbv where

open import framework

postulate
  𝒱 : □
  [_] : 𝒱 → tp pos
  _→cbv_ : 𝒱 → 𝒱 → 𝒱

  [→cbv] : ∀ {α β} → [ α →cbv β ] ≡ U (Π [ α ] λ _ → ▷ (F [ β ]))
  {-# REWRITE [→cbv] #-}

lam : (α β : 𝒱) → (val [ α ] → cmp (F [ β ])) → cmp (F [ α →cbv β ])
lam _ _ M = ret (λ x → ▷/inv (M x))

app : (α β : 𝒱) → cmp (F [ α →cbv β ]) → cmp (F [ α ]) → cmp (F [ β ])
app α β M N =
  bind (F [ β ]) N λ x →
  bind (F _) M λ f →
  ▷/dir (f x)

_ : {α β : 𝒱} {f : val [ α ] → cmp (F [ β ])} {u : val [ α ]} → app α β (lam α β f) (ret u) ≡ step (F [ β ]) (f u)
_ = refl
