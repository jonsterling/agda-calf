{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import Data.Nat.Base
open import Univ

-- Built-in notion of thunkability from fire triangle 
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
  
  ℰℓ/ret : ∀ {k Â} → ℰℓ k (ret Â) (th/ret Â) ≡ F̂ Â
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

compatible : ∀ {A X} → (cmp (F A) → cmp X) → (cmp (F A)) → □ 
compatible {A} {X} f t = (bind X t λ a → f (ret a)) ≡ f t

thunkable : ∀ {A} → cmp (F A)→ □ 
thunkable {A} t = ∀ {X} → (f : cmp (F A) → cmp X) → compatible {A} {X} f t

postulate
  th/thunkable : ∀ {A} → (t : cmp (F A)) → th (F A) t → thunkable {A} t
    
-- type level versions
compatible/tp : ∀ {A} → (cmp (F A) → tp neg) → (cmp (F A)) → □ 
compatible/tp {A} f t = (tbind t (λ a → f (ret a))) ≡ f t

thunkable/tp : ∀ {A} → cmp (F A)→ □ 
thunkable/tp {A} t = ∀ (f : cmp (F A) → tp neg) → compatible/tp {A} f t

postulate
  th/thunkable/tp : ∀ {A} → (t : cmp (F A)) → th (F A) t → thunkable/tp {A} t

postulate
  th⁻ : (B : tp neg) → cmp B → tp neg 
  th⁻/decode : ∀ {B e} → val (U (th⁻ B e)) ≡ th B e
{-# REWRITE th⁻/decode #-}

postulate
  th⁻/code : ∀ {k} (B̂ : cmp (univ neg k)) → cmp (el⁻ _ B̂) → cmp (univ neg k)
  th⁻/code/decode : ∀ {k B̂ e} → el⁻ k (th⁻/code B̂ e) ≡ th⁻ (el⁻ _ B̂) e
{-# REWRITE th⁻/code/decode #-}

postulate
  th/uni : ∀ {B e} → (t1 t2 : th B e) → t1 ≡ t2