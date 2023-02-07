{-# OPTIONS --prop --rewriting #-}

module Examples.Sequence where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ²-ParCostMonoid)

parCostMonoid = ℕ²-ParCostMonoid
open ParCostMonoid parCostMonoid

open import Calf costMonoid
open import Calf.ParMetalanguage parCostMonoid
open import Calf.Types.Unit
open import Calf.Types.Sum
open import Calf.Types.Eq
open import Calf.Types.Nat
open import Data.Nat as N using (_+_)
open import Data.Nat.Properties as N
open import Calf.Types.Bounded costMonoid

open import Function

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; module ≡-Reasoning)


example : cmp [ F nat ∣ ext ↪ (λ _ → ret 3) ]
example = step (F nat) (1 , 1) (ret 3) , step/ext (F nat) (ret 3) (1 , 1)


import Algebra.Structures as A

variable
  A B C : tp pos
  X Y Z : tp neg
  P Q : val A → tp neg

lift₁ : cmp (Π A λ _ → X) → cmp (Π (U (F A)) λ _ → X)
lift₁ {X = X} f e = bind X e f

lift₂ : cmp (Π A λ _ → Π B λ _ → X) → cmp (Π (U (F A)) λ _ → Π (U (F B)) λ _ → X)
lift₂ {X = X} f e₁ e₂ = bind X e₁ λ v₁ → bind X e₂ λ v₂ → f v₁ v₂

-- record Pure (A : tp pos) : Set where
--   field
--     e : cmp (F A)
--     v : ◯ (val A)
--     h : (u : ext) → e ≡ ret (v u)

-- pure : tp pos → tp neg
-- pure A = meta (Pure A)

record SEQUENCE_CORE : Set₁ where
  field
    Seq : tp pos → tp pos

    -- data Seq (A : Set) : Set where
    --   singleton : A → Seq A
    --   empty : Seq A
    --   append : Seq A → Seq A → Seq A
    --   assoc : (x y z : Seq A) → append (append x y) z ≡ append x (append y z)
    --   idˡ : (x : Seq A) → append empty x ≡ x
    --   idʳ : (x : Seq A) → append x empty ≡ x

    singleton/spec : ◯ ((a : val A) → val (Seq A))
    empty/spec : ◯ (val (Seq A))
    append/spec : ◯ ((s₁ s₂ : val (Seq A)) → val (Seq A))
    isMonoid : (u : ext) → A.IsMonoid {A = val (Seq A)} _≡_ (append/spec u) (empty/spec u)

    singleton : cmp (Π A λ a → [ F (Seq A) ∣ ext ↪ (λ u → ret (singleton/spec u a)) ])
    empty : cmp [ F (Seq A) ∣ ext ↪ (λ u → ret (empty/spec u)) ]
    append : cmp (Π (Seq A) λ s₁ → Π (Seq A) λ s₂ → [ F (Seq A) ∣ ext ↪ (λ u → ret (append/spec u s₁ s₂)) ])

    mapreduce :
      {X : tp neg}
      → (f : cmp (Π A λ _ → X))
      → (z : cmp X)
      → (g : cmp (Π (U X) λ _ → Π (U X) λ _ → X))
      → ◯ (A.IsMonoid _≡_ g z)
      → val (Seq A)
      → cmp X

    mapreduce/singleton : ∀ {f z g h a}     → (u : ext) → mapreduce {X = X} f z g h (singleton/spec {A} u a ) ≡ f a
    mapreduce/empty     : ∀ {f z g h}       → (u : ext) → mapreduce {X = X} f z g h (empty/spec {A} u       ) ≡ z
    mapreduce/append    : ∀ {f z g h s₁ s₂} → (u : ext) → mapreduce {X = X} f z g h (append/spec {A} u s₁ s₂) ≡ g (mapreduce {X = X} f z g h s₁) (mapreduce {X = X} f z g h s₂)

    -- induction :
    --   {P : ◯ (val (Seq A)) → tp neg}
    --   → cmp (Π A λ a → P λ u → Pure.v (singleton a) u)
    --   → (z : cmp (P λ u → Pure.v empty u))
    --   → (g : cmp (Π (Seq A) λ s₁ → Π (Seq A) λ s₂ → Π (U (P λ u → s₁)) λ _ → Π (U (P λ u → s₂)) λ _ → P λ u → Pure.v (append s₁ s₂) u))
    --   → ((u : ext) → cmp (Π (Seq A) λ s → Π (U (P λ u → s)) λ h → {!   !}))
    --   → (s : val (Seq A))
    --   → cmp (P λ u → s)

    -- -- induction/singleton : ∀ {P f z g h a}     → ◯ (dbind P (singleton {A} a ) (induction {P = P} f z g h) ≡ f a)
    -- -- induction/empty     : ∀ {P f z g h}       → ◯ (dbind P (empty {A}       ) (induction {P = P} f z g h) ≡ z)
    -- -- induction/append    : ∀ {P f z g h s₁ s₂} → ◯ (dbind P (append {A} s₁ s₂) (induction {P = P} f z g h) ≡ g s₁ s₂ (induction {P = P} f z g h s₁) (induction {P = P} f z g h s₂))

module Example (S : SEQUENCE_CORE) where
  open SEQUENCE_CORE S

  id-traverse : cmp (Π (Seq A) λ s → F (Seq A))
  id-traverse {A = A} =
    mapreduce
      {X = F (Seq A)}
      (proj₁ ∘ singleton)
      z
      g
      h
    where
      z : cmp (F (Seq A))
      z = proj₁ empty

      g : cmp (Π (U (F (Seq A))) λ _ → Π (U (F (Seq A))) λ _ → F (Seq A))
      g = lift₂ {X = F (Seq A)} λ s₁ s₂ → proj₁ (append s₁ s₂)

      h₁ : ◯ ((s : cmp (F (Seq A))) → g z s ≡ s)
      h₁ u s rewrite proj₂ (empty {A}) u =
        begin
          (bind (F (Seq A)) s λ v₂ → proj₁ (append (empty/spec u) v₂))
        ≡⟨
          Eq.cong (bind (F (Seq A)) s) (funext λ v₂ →
            begin
              proj₁ (append (empty/spec u) v₂)
            ≡⟨ proj₂ (append (empty/spec u) v₂) u ⟩
              ret (append/spec u (empty/spec u) v₂)
            ≡⟨ Eq.cong ret (A.IsMonoid.identityˡ (isMonoid S u) v₂) ⟩
              ret v₂
            ∎
          )
        ⟩
          bind (F (Seq A)) s ret
        ≡⟨⟩
          s
        ∎
          where open ≡-Reasoning

      h₂ : ◯ ((s : cmp (F (Seq A))) → g s z ≡ s)
      h₂ u s rewrite proj₂ (empty {A}) u =
        begin
          (bind (F (Seq A)) s λ v₁ → proj₁ (append v₁ (empty/spec u)))
        ≡⟨
          Eq.cong (bind (F (Seq A)) s) (funext λ v₁ →
            begin
              proj₁ (append v₁ (empty/spec u))
            ≡⟨ proj₂ (append v₁ (empty/spec u)) u ⟩
              ret (append/spec u v₁ (empty/spec u))
            ≡⟨ Eq.cong ret (A.IsMonoid.identityʳ (isMonoid S u) v₁) ⟩
              ret v₁
            ∎
          )
        ⟩
          bind (F (Seq A)) s ret
        ≡⟨⟩
          s
        ∎
          where open ≡-Reasoning

      h : ◯ (A.IsMonoid _≡_ g z)
      h u =
        record
          { isSemigroup =
              record
                { isMagma =
                    record
                      { isEquivalence = Eq.isEquivalence
                      ; ∙-cong = Eq.cong₂ g
                      }
                ; assoc = λ s₁ s₂ s₃ →
                    let open ≡-Reasoning in
                    begin
                      g (g s₁ s₂) s₃
                    ≡⟨⟩
                      ( bind (F (Seq A)) s₁ λ v₁ →
                        bind (F (Seq A)) s₂ λ v₂ →
                        bind (F (Seq A)) (proj₁ (append v₁ v₂)) λ v₁₂ →
                        bind (F (Seq A)) s₃ λ v₃ →
                        proj₁ (append v₁₂ v₃))
                    ≡⟨
                      Eq.cong (bind (F (Seq A)) s₁) (funext λ v₁ →
                      Eq.cong (bind (F (Seq A)) s₂) (funext λ v₂ →
                      begin
                        ( bind (F (Seq A)) (proj₁ (append v₁ v₂)) λ v₁₂ →
                          bind (F (Seq A)) s₃ λ v₃ →
                          proj₁ (append v₁₂ v₃))
                      ≡⟨
                        Eq.cong
                          (λ e →
                            bind (F (Seq A)) e λ v₁₂ →
                            bind (F (Seq A)) s₃ λ v₃ →
                            proj₁ (append v₁₂ v₃))
                          (proj₂ (append v₁ v₂) u)
                      ⟩
                        ( bind (F (Seq A)) s₃ λ v₃ →
                          proj₁ (append (append/spec u v₁ v₂) v₃))
                      ≡⟨
                        Eq.cong (bind (F (Seq A)) s₃) (funext λ v₃ →
                        begin
                          proj₁ (append (append/spec u v₁ v₂) v₃)
                        ≡⟨ proj₂ (append _ v₃) u ⟩
                          ret (append/spec u (append/spec u v₁ v₂) v₃)
                        ≡⟨ Eq.cong ret (A.IsMonoid.assoc (isMonoid S u) v₁ v₂ v₃) ⟩
                          ret (append/spec u v₁ (append/spec u v₂ v₃))
                        ≡˘⟨ proj₂ (append v₁ _) u ⟩
                          proj₁ (append v₁ (append/spec u v₂ v₃))
                        ≡˘⟨
                          Eq.cong
                            (λ e → bind (F (Seq A)) e λ v₂₃ → proj₁ (append v₁ v₂₃))
                            (proj₂ (append v₂ v₃) u)
                        ⟩
                          ( bind (F (Seq A)) (proj₁ (append v₂ v₃)) λ v₂₃ →
                            proj₁ (append v₁ v₂₃))
                        ∎)
                      ⟩
                        ( bind (F (Seq A)) s₃ λ v₃ →
                          bind (F (Seq A)) (proj₁ (append v₂ v₃)) λ v₂₃ →
                          proj₁ (append v₁ v₂₃))
                      ∎))
                    ⟩
                      ( bind (F (Seq A)) s₁ λ v₁ →
                        bind (F (Seq A)) s₂ λ v₂ →
                        bind (F (Seq A)) s₃ λ v₃ →
                        bind (F (Seq A)) (proj₁ (append v₂ v₃)) λ v₂₃ →
                        proj₁ (append v₁ v₂₃))
                    ≡⟨⟩
                      g s₁ (g s₂ s₃)
                    ∎
                }
          ; identity = h₁ u , h₂ u
          }

  head : cmp (Π (Seq A) λ s → F (sum A unit))
  head {A = A} = mapreduce {X = F (sum A unit)} (ret ∘ inj₁) z g h
    where
      z : cmp (F (sum A unit))
      z = ret (inj₂ triv)

      g-aux : cmp (Π (sum A unit) λ _ → Π (U (F (sum A unit))) λ _ → F (sum A unit))
      g-aux (inj₁ a   ) e₂ = ret (inj₁ a)
      g-aux (inj₂ triv) e₂ = e₂

      g : cmp (Π (U (F (sum A unit))) λ _ → Π (U (F (sum A unit))) λ _ → F (sum A unit))
      g e₁ e₂ = bind (F (sum A unit)) e₁ λ v₁ → g-aux v₁ e₂

      h : ◯ (A.IsMonoid _≡_ g z)
      h u =
        record
          { isSemigroup =
              record
                { isMagma =
                    record
                      { isEquivalence = Eq.isEquivalence
                      ; ∙-cong = Eq.cong₂ g
                      }
                ; assoc = λ e₁ e₂ e₃ →
                    Eq.cong
                      (bind (F (sum A unit)) e₁)
                      {x = λ v₁ → bind (F (sum A unit)) (g-aux v₁ e₂) λ v₂ → g-aux v₂ e₃}
                      {y = λ v₁ → g-aux v₁ (bind (F (sum A unit)) e₂ λ v₂ → g-aux v₂ e₃)}
                      (funext λ
                        { (inj₁ a   ) → refl
                        ; (inj₂ triv) → refl})
                }
          ; identity =
              (λ e → refl) ,
              (λ e →
                Eq.cong
                  (bind (F (sum A unit)) e)
                  {x = λ v₁ → g-aux v₁ (ret (inj₂ triv))}
                  {y = ret}
                  (funext λ
                    { (inj₁ a   ) → refl
                    ; (inj₂ triv) → refl }))
          }


--   example₀ : ◯ (id-traverse {A = A} ≡ ret)
--   example₀ {A = A} u = funext λ s →
--     let open ≡-Reasoning in
--     induction
--       {P = λ s → meta (id-traverse (s u) ≡ ret (s u))}
--       (λ a →
--         begin
--           id-traverse (Pure.v (singleton a) u)
--         ≡⟨ mapreduce/singleton u ⟩
--           Pure.e (singleton a)
--         ≡⟨ Pure.h (singleton a) u ⟩
--           ret (Pure.v (singleton a) u)
--         ∎)
--       ( begin
--           id-traverse (Pure.v empty u)
--         ≡⟨ mapreduce/empty u ⟩
--           Pure.e empty
--         ≡⟨ Pure.h empty u ⟩
--           ret (Pure.v empty u)
--         ∎
--       )
--       (λ s₁ s₂ ih₁ ih₂ →
--           begin
--             id-traverse (Pure.v (append s₁ s₂) u)
--           ≡⟨ mapreduce/append u ⟩
--             lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂)) (id-traverse s₁) (id-traverse s₂)
--           ≡⟨ Eq.cong₂ (lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂))) ih₁ ih₂ ⟩
--             lift₂ {X = F (Seq A)} (λ v₁ v₂ → Pure.e (append v₁ v₂)) (ret {Seq A} s₁) (ret {Seq A} s₂)
--           ≡⟨⟩
--             Pure.e (append s₁ s₂)
--           ≡⟨ Pure.h (append s₁ s₂) u ⟩
--             ret (Pure.v (append s₁ s₂) u)
--           ∎
--         )
--       {!   !}
--       s

--   id-traverse' : cmp (Π (Seq A) λ s → pure (Seq A))
--   id-traverse' {A = A} = mapreduce {X = pure (Seq A)} singleton empty {!   !} {!   !}
--     -- where
--       -- h₁ : ◯ ((s : val (U (F (Seq A)))) → (bind (F (Seq A)) (Pure.e empty) λ v₁ → bind (F (Seq A)) s λ v₂ → Pure.e (append v₁ v₂)) ≡ s)
--       -- h₁ u s rewrite Pure.h (empty {A = A}) u =
--       --   begin
--       --     (bind (F (Seq A)) s λ v₂ → Pure.e (append (Pure.v empty u) v₂))
--       --   ≡⟨
--       --     Eq.cong (bind _ s) (funext λ v₂ →
--       --       begin
--       --         Pure.e (append (Pure.v empty u) v₂)
--       --       ≡⟨ Pure.h (append (Pure.v empty u) v₂) u ⟩
--       --         ret (Pure.v (append (Pure.v empty u) v₂) u)
--       --       ≡⟨ Eq.cong ret (A.IsMonoid.identityˡ (isMonoid S u) v₂) ⟩
--       --         ret v₂
--       --       ∎
--       --     )
--       --   ⟩
--       --     bind (F (Seq A)) s ret
--       --   ≡⟨ {!   !} ⟩
--       --     s
--       --   ∎
--       --     where open ≡-Reasoning

--       -- h : ◯ (A.IsMonoid _≡_ append empty)
--       -- h u = ?
--       -- h u rewrite Pure.h {!   !} u =
--       --   record
--       --     { isSemigroup =
--       --         record
--       --           { isMagma = {!   !}
--       --           ; assoc = {!   !}
--       --           }
--       --     ; identity = h₁ u , {!   !}
--       --     }

--   -- map : cmp (Π (U (Π A λ _ → F B)) λ _ → Π (Seq A) λ _ → F (Seq B))
--   -- map {B = B} f =
--   --   mapreduce {X = F (Seq B)}
--   --     (lift₁ {X = F (Seq B)} singleton ∘ f)
--   --     empty
--   --     (lift₂ {X = F (Seq B)} append)
--   --     (isMonoid S)

--   -- sum : cmp (Π (Seq nat) λ _ → F nat)
--   -- sum =
--   --   mapreduce {X = F nat}
--   --     ret
--   --     (ret 0)
--   --     (lift₂ {X = F nat} λ n₁ n₂ → ret (n₁ + n₂))
--   --     record
--   --       { isSemigroup =
--   --           record
--   --             { isMagma =
--   --               record { isEquivalence =
--   --                   record
--   --                     { refl = λ u → refl
--   --                     ; sym = λ h u → Eq.sym (h u)
--   --                     ; trans = λ h₁ h₂ u → Eq.trans (h₁ u) (h₂ u)
--   --                     }
--   --                 ; ∙-cong = λ h₁ h₂ u → Eq.cong₂ (lift₂ (λ n₁ n₂ → ret (n₁ + n₂))) (h₁ u) (h₂ u)
--   --                 }
--   --               ; assoc = λ n₁ n₂ n₃ u → Eq.cong (bind (F (U (meta ℕ))) n₁) (funext (λ v₁ → Eq.cong (bind (F nat) n₂) (funext (λ v₂ → Eq.cong (bind (F nat) n₃) (funext (λ v₃ → Eq.cong ret (+-assoc v₁ v₂ v₃))))))) }
--   --               ; identity = (λ n u → {!   !}) , λ n u → {!   !} }

--   -- reverse : cmp (Π (Seq A) λ _ → F (Seq A))
--   -- reverse {A = A} =
--   --   mapreduce {X = F (Seq A)}
--   --     singleton
--   --     empty
--   --     (λ s₁ s₂ → lift₂ {X = F (Seq A)} append s₂ s₁)
--   --     {!   !}

--   -- example₁ : (f : cmp (Π A λ _ → F B)) (s : val (Seq A)) → lift₁ {X = F (Seq B)} (map f) (reverse s) ≡ lift₁ {X = F (Seq B)} reverse (map f s)
--   -- example₁ = {!   !}

--   -- example₂ : (s : val (Seq nat)) → bind (F nat) (reverse s) sum ≡ sum s
--   -- example₂ = {!   !}
