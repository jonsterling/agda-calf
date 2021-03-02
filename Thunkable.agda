{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import Data.Nat.Base
open import Univ

-- Built-in notion of thunability from fire triangle 
-- (Fig. 8, p.17). Thunkability judgment (th) is not part of the connectives as originally 
-- described.
postulate
  th : (t : tp neg) → cmp t → □
  th/ret : ∀ {A} → (v : val A) → th (F A) (ret v)
  th/bind : ∀ {A X} → (e : cmp (F A)) → (f : val A → cmp X) → 
    th (F A) e → 
    ((a : val A) → th X (f a)) → 
    th X (bind X e f)
  th/dbind : ∀ {A X} → (e : cmp (F A)) → (f : (a : val A) → cmp (X a)) → 
    th (F A) e → 
    ((a : val A) → th (X a) (f a)) → 
    th (tbind e X) (dbind X e f) 

  El : (k : ℕ) → (X : cmp (F (univ pos k))) → th (F (univ pos k)) X → val (univ pos k)
  ℰℓ : (k : ℕ) → (X : cmp (F (univ pos k))) → th (F (univ pos k)) X → cmp (univ neg k)
  ⇑ : ∀ {k} → (X : cmp (F (univ pos k))) → (h : th (F (univ pos k)) X) → 
    (t : cmp (el⁻ k (ℰℓ k X h))) → th (el⁻ k (ℰℓ k X h)) t → val (el⁺ k (El k X h))
  ⇓ : ∀ {k} → (X : cmp (F (univ pos k))) → (h : th (F (univ pos k)) X) → 
    val (el⁺ k (El k X h)) → 
    cmp (el⁻ k (ℰℓ k X h))
    
  th/⇓ : ∀ {k} → (X : cmp (F (univ pos k))) → (h : th (F (univ pos k)) X) → 
    (v : val (el⁺ k (El k X h))) → 
    th (el⁻ k (ℰℓ k X h)) (⇓ X h v)
  -- ℰℓ/decode : ∀ {k} → (X : cmp (F (univ pos k))) → (h : th (F (univ pos k)) X) → 
  --   el⁻ k (ℰℓ k X h) ≡ (tbind X λ u → F (el⁺ k u))
  -- {-# REWRITE ℰℓ/decode #-}
  
  ℰℓ/ret : ∀ {k A} → el⁻ k (ℰℓ k (ret A) (th/ret A)) ≡ F (el⁺ k A)
  {-# REWRITE ℰℓ/ret #-}

  -- codomain are the thunkable types at level k.
  Θ : ∀ {l k} → (h : k < l) → (A : val (univ pos k)) → 
    (val (el⁺ k A) → val (el⁺ l (El l (ret (Û⁺ {l} {k} h)) (th/ret _)))) → 
    val (univ pos l)
  -- lower case theta
  θ : ∀ {l k} → (h : k < l) → (A : val (univ pos k)) → 
    (B : val (el⁺ k A) → val (el⁺ l (El l (ret (Û⁺ {l} {k} h)) (th/ret _)))) → 
    (f : (a : val (el⁺ k A)) → val (el⁺ k (El k (⇓ (ret (Û⁺ {l} {k} h)) (th/ret _) (B a)) (th/⇓ _ _ (B a)) ))) → 
    val (el⁺ l (Θ h A B))
  ap : ∀ {l k} → (h : k < l) → (A : val (univ pos k)) → 
    (B : val (el⁺ k A) → val (el⁺ l (El l (ret (Û⁺ {l} {k} h)) (th/ret _)))) → 
    val (el⁺ l (Θ h A B)) → 
    (a : val (el⁺ k A)) → 
    val (el⁺ k (El k (⇓ _ _ (B a)) (th/⇓ _ _ _)))

  Θ/beta : ∀ {l k} → (h : k < l) → (A : val (univ pos k)) → 
    (B : val (el⁺ k A) → val (el⁺ l (El l (ret (Û⁺ {l} {k} h)) (th/ret _)))) → 
    (f : (a : val (el⁺ k A)) → val (el⁺ k (El k (⇓ (ret (Û⁺ {l} {k} h)) (th/ret _) (B a)) (th/⇓ _ _ (B a)) ))) → 
    (a : val (el⁺ k A)) → 
    ap h A B (θ h A B f) a ≡ f a 
  {-# REWRITE Θ/beta #-}

  ⇓/⇑ : ∀ {k} → (X : cmp (F (univ pos k))) → (h : th (F (univ pos k)) X) → 
    (t : cmp (el⁻ k (ℰℓ k X h))) → (h1 : th (el⁻ k (ℰℓ k X h)) t) → 
    ⇓ X h (⇑ X h t h1) ≡ t
  {-# REWRITE ⇓/⇑ #-}




    