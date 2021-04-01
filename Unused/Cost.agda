{-# OPTIONS --prop --rewriting #-}

open import Prelude
open import Metalanguage
open import PhaseDistinction
open import Eq
open import Thunkable
open import Univ
open import Unit
open import Void
open import Data.Product.Properties
open import Function.Bundles
open import Data.Nat
open import Data.Nat.Properties

infixr 10 _⇒_
_⇒_ : tp pos → tp neg → tp neg
A ⇒ B = Π A (λ _ → B)

-- pure : tp pos → tp neg
-- pure A = Σ+- (U (F A)) λ c → th⁻ (F A) c

-- pure/code : ∀ {k} → val (univ pos k) → cmp (univ neg k)
-- pure/code Â = Σ+-/code (Û (F̂ Â)) λ c → th⁻/code (F̂ Â) c

-- add : cmp (Π nat (λ _ → Π nat (λ _ → F nat)))
-- add = λ n → λ m → rec n (λ _ → F nat) (ret m) (λ _ r → bind (F nat) r  λ k → ret(suc k))

-- add/th : ∀ {n1 n2} → th (F nat) (add n1 n2)
-- add/th {n1} {n2} = (th/rec n1 (λ _ → nat) (ret n2) ((λ _ r → bind (F nat) r  λ k → ret(suc k)))
--   (th/ret n2) (λ n r h → th/bind r (λ k → ret(suc k)) h λ a → th/ret _))

-- add/cmp : cmp (U(F nat) ⇒ U(F nat) ⇒ F nat)
-- add/cmp =
  -- λ c1 c2 →
--   bind (F nat) c1 λ n1 →
--   bind (F nat) c2 λ n2 →
--   add n1 n2

-- add/cmp/th : ∀ {c1 c2} → th (F nat) c1 → th (F nat) c2 → th (F nat) (add/cmp c1 c2)
-- add/cmp/th {c1} {c2} h1 h2 =
--   (th/bind _ _ h1 (λ n1 → th/bind _ _ h2 (λ n2 → add/th {n1} {n2})))

-- infixr 20 _⊕_

-- cost is an extensional (computation of a nat with the proof that it is thunkable)
-- question: is this really necessary, since under open all steps are erased anyway?
-- i.e., is this sound: postulate th/open : ∀ {B e} → ◯ (thunkable {B} e)
-- cost/zero : cmp
-- cost/zero = λ u → ret zero

-- add/cost : cmp (U 𝒞 ⇒ U 𝒞 ⇒ 𝒞)
-- add/cost c1 c2 u = add/cmp (c1 u) (c2 u)


-- Arithmetic. This can be defined as an inductive type if that is available.
-- Otherwise it can also be a type computation, which requires universes.



-- postulate
--   lt : cmp (nat ⇒ nat ⇒ univ neg 0)

-- le/cmp : cmp (F nat) → cmp (F nat) → tp neg
-- le/cmp c1 c2 =
--   tbind c1 λ n1 →
--   tbind c2 λ n2 →
--   el⁻ _ (le n1 n2)

-- le/cost : cmp 𝒞 → cmp 𝒞 → tp neg
-- le/cost p q = ext/cmp (λ u → le/cmp (p u) (q u))

-- lt/cmp : cmp (pure nat) → cmp (pure nat) → cmp (univ neg 0)
-- lt/cmp (c1 , _) (c2 , _) =
--   bind (univ neg 0) c1 λ n1 →
--   bind (univ neg 0) c2 λ n2 →
--   lt n1 n2

-- lt/ext : cmp 𝒞 → cmp 𝒞 → tp neg
-- lt/ext p q = ext/cmp (λ u → lt/cmp (p u) (q u))

-- Just assume arithmetic is true. Equations should be expressed using an equality type, but since
-- I am using equality reflection this is equivalent (*).
-- postulate
--   add/comm : ∀ {n m : val nat} → add n m ≡ add m n
--   le/add : ∀ {n1 n2 m1 m2} → cmp (el⁻ _ (le n1 m1)) → cmp (el⁻ _ (le n2 m2)) → cmp (le/cmp (add n1 n2) (add m1 m2))
--   le/refl : ∀ {n} → cmp (el⁻ _ (le n n))

-- this doesn't work because agda decodes the type code when I rewrite the thunkability
-- equation, which makes the equation inapplicable to the goal. At least this is what I
-- think is happening.
-- add/comm/cmp : ∀ {c1 c2} → th (F nat) c1 → th (F nat) c2 →
--   cmp (el⁻ 0 (F̂ (eq/code (Û (F̂ nat/code)) (add/cmp c1 c2) (add/cmp c2 c1))))
-- add/comm/cmp {c1} {c2} h1 h2 = let h = th/thunkable _ h1 {X = univ neg 0} (λ c1 → (F̂ (eq/code (Û (F̂ nat/code)) (add/cmp c1 c2) (add/cmp c2 c1))))
-- in {!  !}

-- this works :)
-- add/comm/cmp : ∀ {c1 c2} → th (F nat) c1 → th (F nat) c2 →
--   cmp (F (eq (U (F nat)) (add/cmp c1 c2) (add/cmp c2 c1)))
-- add/comm/cmp {c1} {c2} h1 h2 with F (eq (U (F nat)) (add/cmp c1 c2) (add/cmp c2 c1)) | symm (th/thunkable/tp _ h1 (λ c1 → F (eq (U (F nat)) (add/cmp c1 c2) (add/cmp c2 c1))))
-- ... | _ | refl with (tbind c1 λ n1 → F (eq (U (F nat)) (add/cmp (ret n1) c2) (add/cmp c2 (ret n1)))) | symm (th/thunkable/tp _ h2 (λ c2 → tbind c1 λ n1 → F (eq (U (F nat)) (add/cmp (ret n1) c2) (add/cmp c2 (ret n1)))))
-- ...               | _ | refl =
--   dbind _ c2 λ n2 →
--   dbind _ c1 λ n1 →
--   ret (eq/intro (add/comm {n1} {n2}))

-- Requires equality reflection on computations of eq, since
-- equality of (pure) nat computations is itself a computation.
-- add/comm/cost : ∀ {p q} → cmp (F (eq (U 𝒞) (p ⊕ q) (q ⊕ p)))
-- add/comm/cost {p} {q} =
--   (ret (eq/intro (funext/Ω (λ u → Inverse.f Σ-≡,≡↔≡
--     (eq/ref (add/comm/cmp {p u} {q u} (p u . snd) (q u . snd)) , th/uni _ _)))))

-- -- ??? there's gotta be a better way of writing this
-- le/add/cmp' : ∀ {c1 c2 d1 d2} →
--   th (F nat) c1 →
--   th (F nat) c2 →
--   th (F nat) d1 →
--   th (F nat) d2 →
--   cmp (F (U (U(le/cmp c1 d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp c1 c2) (add/cmp d1 d2))))
-- le/add/cmp' {c1} {c2} {d1} {d2} h1 h2 h3 h4 with (F(U(U(le/cmp c1 d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp c1 c2) (add/cmp d1 d2)))) | (th/thunkable/tp _ h1 (λ c1 → F(U(U(le/cmp c1 d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp c1 c2) (add/cmp d1 d2)))))
-- ... | _ | refl with (tbind c1 λ n1 → F(U(U(le/cmp (ret n1) d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp (ret n1) c2) (add/cmp d1 d2)))) | th/thunkable/tp _ h2 (λ c2 → tbind c1 λ n1 → F(U(U(le/cmp (ret n1) d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp (ret n1) c2) (add/cmp d1 d2))))
-- ... | _ | refl with (tbind c2 λ n2 → tbind c1 λ n1 → F(U(U(le/cmp (ret n1) d1) ⇒ U(le/cmp (ret n2) d2) ⇒ le/cmp (add/cmp (ret n1) (ret n2)) (add/cmp d1 d2)))) | th/thunkable/tp _ h3 (λ d1 → tbind c2 λ n2 → tbind c1 λ n1 → F(U(U(le/cmp (ret n1) d1) ⇒ U(le/cmp (ret n2) d2) ⇒ le/cmp (add/cmp (ret n1) (ret n2)) (add/cmp d1 d2))))
-- ... | _ | refl with (tbind d1 λ m1 → tbind c2 λ n2 → tbind c1 λ n1 → F(U(U(le/cmp (ret n1) (ret m1)) ⇒ U(le/cmp (ret n2) d2) ⇒ le/cmp (add/cmp (ret n1) (ret n2)) (add/cmp (ret m1) d2)))) | th/thunkable/tp _ h4 (λ d2 → tbind d1 λ m1 → tbind c2 λ n2 → tbind c1 λ n1 → F(U(U(le/cmp (ret n1) (ret m1)) ⇒ U(le/cmp (ret n2) d2) ⇒ le/cmp (add/cmp (ret n1) (ret n2)) (add/cmp (ret m1) d2))))
-- ... | _ | refl =
--   dbind _ d2 λ m2 →
--   dbind _ d1 λ m1 →
--   dbind _ c2 λ n2 →
--   dbind _ c1 λ n1 →
--    ret (λ g1 g2 → le/add {n1} {n2} {m1} {m2} g1 g2)

-- le/add/cmp : ∀ {c1 c2 d1 d2} →
--   th (F nat) c1 →
--   th (F nat) c2 →
--   th (F nat) d1 →
--   th (F nat) d2 →
--   cmp (U(le/cmp c1 d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp c1 c2) (add/cmp d1 d2))
-- le/add/cmp {c1} {c2} {d1} {d2} h1 h2 h3 h4 = bind (U(le/cmp c1 d1) ⇒ U(le/cmp c2 d2) ⇒ le/cmp (add/cmp c1 c2) (add/cmp d1 d2)) (le/add/cmp' h1 h2 h3 h4) λ f → f

-- le/add/cost : ∀ {p1 p2 q1 q2} → cmp (le/cost p1 q1) → cmp (le/cost p2 q2) → cmp (le/cost (p1 ⊕ p2) (q1 ⊕ q2))
-- le/add/cost {p1} {p2} {q1} {q2} h1 h2 = λ u → le/add/cmp {c1 = p1 u . fst} {c2 = p2 u . fst} {d1 = q1 u . fst} {d2 = q2 u . fst} (p1 u . snd) (p2 u . snd) (q1 u . snd) (q2 u . snd) (h1 u) (h2 u)

-- le/zero/cmp' : ∀ {c} → th (F nat) c → cmp (F(U(le/cmp (ret zero) c)))
-- le/zero/cmp' {c} h with (F(U(le/cmp (ret zero) c))) | th/thunkable/tp _ h (λ c → F(U(le/cmp (ret zero) c)))
-- ... | _ | refl =
--   dbind _ c λ n →
--   ret (ret triv)

-- le/zero/cmp : ∀ {c} → th (F nat) c → cmp (le/cmp (ret zero) c)
-- le/zero/cmp {c} h = bind (le/cmp (ret zero) c) (le/zero/cmp' h) λ x → x

-- le/zero/cost : ∀ {p} → cmp (le/cost cost/zero p)
-- le/zero/cost {p} = λ u → le/zero/cmp (p u . snd)

-- le/refl/cmp' : ∀ {c} → th (F nat) c → cmp (F(U(le/cmp c c)))
-- le/refl/cmp' {c} h with (F(U(le/cmp c c))) | th/thunkable/tp _ h (λ c → F(U(le/cmp c c)))
-- ... | _ | refl =
--   dbind _ c λ n →
--   ret (le/refl {n})

-- le/refl/cmp : ∀ {c} → th (F nat) c → cmp (le/cmp c c)
-- le/refl/cmp {c} h = bind (le/cmp c c) (le/refl/cmp' h) λ x → x

-- le/refl/cost : ∀ {p} → cmp (le/cost p p)
-- le/refl/cost {p} = λ u → le/refl/cmp (p u . snd)