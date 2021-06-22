{-# OPTIONS --prop --rewriting #-}

module Examples.Queue where

open import Calf.CostMonoids using (ℕ-CostMonoid)

CostMonoid = ℕ-CostMonoid

open import Calf CostMonoid
open import Calf.Types.Nat CostMonoid
open import Calf.Types.Unit CostMonoid
open import Calf.Types.Sum CostMonoid

open import Data.Nat
open import Data.Nat.Properties
import Data.Integer as Int
import Data.Integer.Properties as IntP
open import Data.List using (List; _∷_; []; length; tabulate) renaming (sum to lsum)
open import Relation.Binary.PropositionalEquality as P

record Queue : Set where
  field
    Q : tp pos
    emp : val Q
    enq : cmp (Π Q λ _ → Π nat λ _ → F Q)
    deq : cmp (Π Q λ _ → F (sum unit (Σ++ Q λ _ → nat)))

-- Suppose we want to implement the Queue signature above using lists.
-- One cost model is to count the number of times a cons node is inspected.
-- This is implemented by the following annotated list type:
-- destructing a cons node of type list n A consumes n steps.
postulate
  list : ∀ (n : ℕ) → tp pos → tp pos
  nil : ∀ {A n} → val (list n A)
  cons : ∀ {A n} → val A → val (list n A) → val (list n A)

  list/ind : ∀ {A n} → (l : val (list n A)) → (X : val (list n A) → tp neg) → cmp (X nil) →
    ((a : val A) → (l : val (list n A)) → (r : val (U (X l))) →
      cmp (X (cons a l))) →
    cmp (X l)
  list/ind/nil : ∀ {A n X} → (e0 : cmp (X nil)) →
      (e1 : (a : val A) → (l : val ((list n A))) → (r : val (U (X l))) →
      cmp (X (cons a l))) →
    list/ind nil X e0 e1 ≡ e0
  {-# REWRITE list/ind/nil #-}
  list/ind/cons : ∀ {A n X} → (a : val A) → (l : val ((list n A))) → (e0 : cmp (X nil)) →
      (e1 : (a : val A) → (l : val ((list n A))) → (r : val (U (X l))) →
      cmp (X (cons a l))) →
    list/ind (cons a l) X e0 e1 ≡ step' (X (cons a l)) n (e1 a l (list/ind l X e0 e1))
  {-# REWRITE list/ind/cons #-}

list/match : ∀ {A n} → (l : val (list n A)) → (X : val (list n A) → tp neg) → cmp (X nil) →
  ((a : val A) → (l : val (list n A)) → cmp (X (cons a l))) →
  cmp (X l)
list/match l X e0 e1 = list/ind l X e0 (λ a l _ → e1 a l)
-- Version of annotated lists using ►. Not so nice to use since the induction principle is behind a tbind :(
-- ►/out : ∀ {A} → val (► A) → cmp (F A)
-- ►/out {A} v = ►/match (F A) v (λ v → ret v)
-- list/rec : ∀ {A} → (l : val (list A)) → (X : tp neg) → cmp X →
--   ((a : val A) → (►/l : val (► (list A))) → (r : val (U (X))) →
--     cmp (X)) →
--   cmp (X)
-- list/rec/nil : ∀ {A X} → (e0 : cmp (X)) →
--     (e1 : (a : val A) → (►/l : val (► (list A))) → (r : val (U X)) →
--     cmp (X)) →
--   list/rec nil X e0 e1 ≡ e0
-- {-# REWRITE list/rec/nil #-}
-- list/rec/cons : ∀ {A X} → (a : val A) → (►/l : val (► (list A))) → (e0 : cmp (X)) →
--     (e1 : (a : val A) → (►/l : val (► (list A))) → (r : val (U (X))) →
--     cmp (X)) →
--   list/rec (cons a ►/l) X e0 e1 ≡ e1 a ►/l (bind X (►/out ►/l) (λ l → list/rec l X e0 e1))
-- {-# REWRITE list/rec/cons #-}

ex : val (list 0 nat)
ex = cons (tonat 0) ((cons (tonat 1) (nil)))

len : ∀ {A n} → val (list n A) → ℕ
len l = list/ind l (λ _ → meta ℕ) 0 λ a l r → 1 + r

-- Implement Queue with a pair of lists; (f , b) represents the queue f :: rev b.
module FrontBack where

  -- For simplicity, we charge 1 step for each cons node destruction.
  L = list 1 nat

  Q : tp pos
  Q = Σ++ L λ _ → L

  emp : val Q
  emp = (nil , nil)

  enq : cmp (Π Q λ _ → Π nat λ _ → F Q)
  enq (f , b) x = ret (f , cons x b)

  enq≤0 : ∀ q x → ub Q (enq q x) 0
  enq≤0 q x = ub/ret 0

  rev/helper : cmp (Π L λ _ → Π L λ _ → F L)
  rev/helper l = list/ind l (λ _ → Π L λ _ → F L)
    (λ a → ret a) λ a _ r → λ l → r (cons a l)

  rev/helper/len : ∀ l → cmp (Π L λ a → meta (len a + len l ≡ bind (meta ℕ) (rev/helper l a) len))
  rev/helper/len l = list/ind l (λ l → Π L λ a → meta (len a + len l ≡ bind (meta ℕ) (rev/helper l a) len))
    (λ x →  +-identityʳ _) (λ x l r → λ a →
    begin
    len a + (1 + len l) ≡⟨ P.sym (+-assoc (len a) 1 (len l)) ⟩
    len a + 1 + len l ≡⟨ P.cong (λ x → x + len l) (+-comm (len a) 1) ⟩
    1 + len a + len l ≡⟨ r (cons x a) ⟩
    bind (meta ℕ) (rev/helper (cons x l) a) len ≡⟨ refl ⟩
    bind (meta ℕ) (rev/helper (cons x l) a) len
    ∎
    )
    where open ≡-Reasoning

  rev/helper/cost = len

  rev/helper≤rev/helper/cost : ∀ l l' → ub L (rev/helper l l') (len l)
  rev/helper≤rev/helper/cost l = list/ind l (λ l → meta (∀ l' → ub L (rev/helper l l') (len l)))
    (λ l' → ub/ret 0)
    (λ a l r → λ l' → subst (ub _ _) (+-comm _ 1) (ub/step {e = rev/helper l (cons a l')} (len l) 1 (r (cons a l'))))

  rev/cost = len

  rev/helper/cons : ∀ l x r → Σ ℕ λ n → Σ (val nat) λ x' → Σ (val L) λ l' → (len l' ≡ len r + len l) × rev/helper (cons x l) r ≡ step' (F L) n (ret (cons x' l'))
  rev/helper/cons l = list/ind l
    (λ l → meta (∀ x r → Σ ℕ λ n → Σ (val nat) λ x' → Σ (val L) λ l' → len l' ≡ len r + len l × rev/helper (cons x l) r ≡ step' (F L) n (ret (cons x' l'))))
    (λ x r → 1 , x , r , P.sym (+-identityʳ (len r)) , refl)
    λ y ys ih → λ x r →
    let (n , x' , l' , eqn1 , eqn2) = ih y (cons x r) in
    1 + n , x' ,  l' ,
    (
      (
      begin
      len l' ≡⟨ eqn1 ⟩
      (1 + len r) + len ys ≡⟨ P.cong (λ x → x + len ys) (+-comm 1 (len r)) ⟩
      len r + 1 + len ys ≡⟨ +-assoc (len r) 1 (len ys) ⟩
      len r + (1 + len ys) ≡⟨ refl ⟩
      len r + (len (cons y ys))
      ∎
      ) ,
     P.cong (λ x → step' (F L) 1 x) {x = (rev/helper (cons y ys) (cons x r))} {y = step' (F L) n (ret (cons x' l'))} eqn2
    )
    where open ≡-Reasoning

  abstract
    rev : cmp (Π L λ _ → F L)
    rev l = rev/helper l nil

    rev/unfold : ∀ l → rev l ≡ rev/helper l nil
    rev/unfold l = refl

    rev/pres/len : ∀ l → len l ≡ bind (meta ℕ) (rev l) len
    rev/pres/len l = rev/helper/len l nil

  rev≤rev/cost : ∀ l → ub L (rev l) (len l)
  rev≤rev/cost l rewrite rev/unfold l = rev/helper≤rev/helper/cost l nil

  rev/ret : ∀ l → Σ ℕ λ n → Σ (val L) λ a → rev l ≡ step' (F L) n (ret a)
  rev/ret l with rev≤rev/cost l
  ... | ub/intro {q = q} a h eqn = q , a , eq/ref eqn

  rev/cons : ∀ x l → Σ ℕ λ n → Σ (val nat) λ x' → Σ (val L) λ l' → len l' ≡ len l × rev (cons x l) ≡ step' (F L) n (ret (cons x' l'))
  rev/cons x l rewrite rev/unfold (cons x l) = rev/helper/cons l x nil

  deq-tp = sum unit (Σ++ Q λ _ → nat)

  deq/emp : val L → cmp (F deq-tp)
  deq/emp = (λ l → list/match l (λ _ → F deq-tp) (ret (inj₁ triv)) λ a l' → ret (inj₂ ((l' , nil) , a)))

  deq : cmp (Π Q λ _ → F deq-tp)
  deq (f , b) = list/match f (λ _ → F deq-tp)
    (bind (F deq-tp) (rev b) deq/emp)
    λ a l → ret (inj₂ ((l , b) , a))

  deq/cost : val Q → ℕ
  deq/cost (f , b) = list/match f (λ _ → meta ℕ) (list/match b (λ _ → meta ℕ) 0 (λ _ b' → 1 + len b)) (λ _ _ → 1)

  deq≤deq/cost : ∀ q → ub deq-tp (deq q) (deq/cost q)
  deq≤deq/cost (f , b) = list/match f (λ f → meta (ub deq-tp (deq (f , b)) (deq/cost (f , b))))
    (list/match b
      (λ b → meta (ub deq-tp (deq (nil , b)) (deq/cost (nil , b))))
      emp/emp
      (λ a l → let (n , rv , eqn) = rev/ret (cons a l) in
      ( emp/cons a l)))
      λ a l → cons/back a l b

    where
    emp/emp : ub deq-tp (deq (nil , nil)) (deq/cost (nil , nil))
    emp/emp rewrite rev/unfold nil = ub/ret 0

    emp/cons : ∀ a l → ub deq-tp (deq (nil , cons a l)) (deq/cost (nil , cons a l))
    emp/cons a l with rev≤rev/cost (cons a l)
    ... | ub/intro {q = n} rv h eqn rewrite rev/pres/len (cons a l)
        | (eq/ref eqn) =
        let g : ∀ rv → (n ≤ len rv) → ub deq-tp (bind (F deq-tp) (step' (F L) n (ret rv)) deq/emp) (1 + len rv)
            g l = list/ind l
                  (λ l → meta (n ≤ len l → ub deq-tp (bind (F deq-tp) (step' (F L) n (ret l)) deq/emp) (1 + len l)))
                  (λ h → let h1 = n≤0⇒n≡0 h in
                   P.subst (λ n → ub deq-tp (step' (F deq-tp) n (ret (inj₁ triv))) 1) (P.sym h1) (ub/ret 1))
                  (λ a l ih → λ h → ub/intro {q = n + 1} (inj₂ ((l , nil) , a))
                    (begin
                    n + 1 ≤⟨ +-monoˡ-≤ 1 h  ⟩
                    len (cons a l) + 1 ≡⟨ +-comm (len (cons a l)) 1 ⟩
                    1 + len (cons a l) ≤⟨ ≤-refl ⟩
                    1 + len (cons a l)
                    ∎
                    )
                    (ret (eq/intro refl)))
        in
        g rv h
      where open ≤-Reasoning

    cons/back : ∀ a l b → ub deq-tp (deq (cons a l , b)) (deq/cost (cons a l , b))
    cons/back a l b = ub/intro {q = 1} (inj₂ ((l , b) , a)) ≤-refl (ret (eq/intro refl))

  -- Amortized analysis for front-back queue.
  -- The goal is to bound the cost of a single-thread sequence of queue operations staring with an initial queue q0,
  -- where an operation is either an enqueue or a dequeue.
  data op : Set where
    op/enq : (x : val nat) → op
    op/deq : op

  -- Potential function
  ϕ : val Q → ℕ
  ϕ (f , b) = len f + 2 * (len b)

  -- o operate q is the computation induced by operation o on queue q.
  -- Needed because deq doesn't always return a queue (e.g., deq emp).
  -- In these cases we just return the empty queue.
  _operate_ : op → val Q → cmp (F Q)
  (op/enq x) operate q = enq q x
  (op/deq) operate q =
    bind (F Q) (deq q) λ s → (sum/case unit (Σ++ Q λ _ → nat) (λ _ → F Q) s
    (λ _ → ret (nil , nil))
    (λ { (q , x) → ret q }))

  -- o operateϕ q is morally ϕ (o operate q), which doesn't type-check since o operate q is a computation.
  -- Easier to work with than bind (meta ℕ) (o operate q) ϕ (but they are equivalent, as shown below).
  _operateϕ_ : op → val Q → ℕ
  (op/enq x) operateϕ (f , b) = len f + 2 * (1 + len b)
  (op/deq) operateϕ (f , b) = list/match f (λ _ → meta ℕ) (list/match b (λ _ → meta ℕ) 0 (λ _ b' → len b')) (λ _ f' → len f' + 2 * len b)

  operateϕ≡ϕ∘operate : ∀ o q → o operateϕ q ≡ bind (meta ℕ) (o operate q) ϕ
  operateϕ≡ϕ∘operate (op/enq x) q = refl
  operateϕ≡ϕ∘operate op/deq (f , b) = list/match f
        (λ f →
          meta
          ((op/deq operateϕ (f , b)) ≡
            bind (meta ℕ) (op/deq operate (f , b)) ϕ))
        (list/ind b (λ b → meta ((op/deq operateϕ (nil , b)) ≡ bind (meta ℕ) (op/deq operate (nil , b)) ϕ))
        (P.subst (λ x → 0 ≡ bind (meta ℕ) (bind (F Q) (bind (F deq-tp) x deq/emp) λ s → (sum/case unit (Σ++ Q λ _ → nat) (λ _ → F Q) s (λ _ → ret (nil , nil)) (λ { (q , x) → ret q }))) ϕ)
        (P.sym (rev/unfold nil)) refl)
        λ a l ih → emp/cons a l)
        λ a l → refl

    where
    emp/cons : ∀ a l → op/deq operateϕ (nil , cons a l) ≡ bind (meta ℕ) (op/deq operate (nil , cons a l)) ϕ
    emp/cons a l with rev/cons a l
    ... | (n , x' , l' , eqn1 , eqn2 ) rewrite eqn2 =
      begin
      len l ≡⟨ P.sym eqn1 ⟩
      len l' ≡⟨ P.sym (+-identityʳ (len l')) ⟩
      len l' + 0 ≡⟨ refl ⟩
      len l' + 0
      ∎
     where open ≡-Reasoning

  -- op/cost o q is the cost of o operate q.
  op/cost : op → val Q → ℕ
  op/cost (op/enq x) q = 0
  op/cost (op/deq) (f , b) = list/match f (λ _ → meta ℕ) (list/match b (λ _ → meta ℕ) 0 (λ _ b' → 2 + len b')) (λ _ _ → 1)

  deq/cost≡cost/deq : ∀ q → deq/cost q ≡ op/cost op/deq q
  deq/cost≡cost/deq (f , b) =
    P.cong (λ x → list/match f (λ _ → meta ℕ) x (λ _ _ → 1)) (list/match b
    (λ b →
      meta
        (list/match b (λ _ → meta ℕ) 0 (λ _ b' → 1 + len b) ≡
          list/match b (λ _ → meta ℕ) 0 (λ _ b' → 2 + len b')))
      refl (λ a l → refl))

  -- cost o q upperbounds the cost of o operate q.
  op≤cost : ∀ o q → ub Q (o operate q) (op/cost o q)
  op≤cost (op/enq x) q = enq≤0 q x
  op≤cost op/deq q rewrite P.sym (+-identityʳ (op/cost (op/deq) q)) = ub/bind/const {A = deq-tp} {e = deq q} {f = λ s → (sum/case unit (Σ++ Q λ _ → nat) (λ _ → F Q) s
    (λ _ → ret (nil , nil))
    (λ { (q , x) → ret q }))} (op/cost op/deq q) 0
    (P.subst (λ x → ub deq-tp (deq q) x) (deq/cost≡cost/deq q) (deq≤deq/cost q))
    λ a → ub/sum/case/const/const unit ((Σ++ Q λ _ → nat)) (λ _ → Q) a ((λ _ → ret (nil , nil))) (λ { (q , x) → ret q }) 0
    (λ _ → ub/ret 0)
    (λ _ → ub/ret 0)

  -- is/acost o k when for any state q, k suffices for the cost of o on q and the difference in the potential.
  is/acost :  op → ℕ → Set
  is/acost o k = ∀ q → (Int.+ (op/cost o q)) Int.+ ((o operateϕ q) Int.⊖ (ϕ q)) Int.≤ Int.+ k

  acost/weaken : ∀ {m n o} → m ≤ n → is/acost o m → is/acost o n
  acost/weaken h1 h2 = λ q → IntP.≤-trans (h2 q) (Int.+≤+ h1)

  -- A sequence of operations induces a single computation by threading through the initial state q0.
  _operate/seq_ : List op → val Q → cmp (F Q)
  [] operate/seq q0 = ret q0
  (o ∷ os) operate/seq q = bind (F Q) (o operate q) λ q' → os operate/seq q'

  cost/seq : ∀ (l : List op) → val Q → ℕ
  cost/seq [] q0 = 0
  cost/seq (o ∷ os) q = bind (meta ℕ) (o operate q) λ q' → op/cost o q + cost/seq os q'

  -- Cost of a sequence computation is bounded by the sum of cost of the constituents.
  operate/seq≤cost/seq : ∀ l q → ub Q (l operate/seq q) (cost/seq l q)
  operate/seq≤cost/seq [] q0 = ub/ret 0
  operate/seq≤cost/seq (o ∷ os) q = ub/bind {A = Q} {e = o operate q} {f = λ q → os operate/seq q}
   (op/cost o q) (cost/seq os) (op≤cost o q) λ q → operate/seq≤cost/seq os q

  -- Telescoping the potential.
  cost/seq/tele : ∀ (l : List op) → val Q → Int.ℤ
  cost/seq/tele [] q0 = Int.0ℤ
  cost/seq/tele (o ∷ os) q = bind (meta Int.ℤ) (o operate q) λ q' → (Int.+ (op/cost o q)) Int.+ (o operateϕ q Int.⊖ ϕ q) Int.+ (cost/seq/tele os q')

  ϕn : ℕ → List op → val Q → ℕ
  ϕn zero l q0 = ϕ q0
  ϕn (suc n) (o ∷ os) q = bind (meta ℕ) (o operate q) λ q' → ϕn n os q'
  ϕn (suc n) [] q = 0

  -- Potential of the initial state
  ϕ/0 : List op → val Q → ℕ
  ϕ/0 l = ϕn 0 l

  -- Potential of the final state
  ϕ/-1 : List op → val Q → ℕ
  ϕ/-1 l = ϕn (length l) l

  bind/dup : ∀ A 𝕊 𝕋 e f (g : val A → 𝕊 → 𝕋) → bind {A} (meta 𝕋) e (λ a → g a (bind {A} (meta 𝕊) e f)) ≡ bind {A} (meta 𝕋) e (λ a → g a (f a))
  bind/dup A 𝕊 𝕋 e f g =
    begin
    bind (meta 𝕋) e (λ a → g a (bind (meta 𝕊) e f)) ≡⟨ P.cong (λ h → bind (meta 𝕋) e h) (funext (λ a → bind/meta A 𝕊 𝕋 e f (λ s → g a s))) ⟩
    bind (meta 𝕋) e (λ a → bind (meta 𝕋) e (λ a' → g a (f a'))) ≡⟨ bind/idem A 𝕋 e (λ a a' → g a (f a')) ⟩
    bind (meta 𝕋) e (λ a → g a (f a)) ≡⟨ refl ⟩
    bind (meta 𝕋) e (λ a → g a (f a))
    ∎
    where open ≡-Reasoning

  -- Telescoping sum:
  -- Σᵢⁿ op/cost oᵢ + ϕ qᵢ - ϕ qᵢ­₋₁ = ϕ q_{n-1} - ϕ q_0 + Σᵢ costᵢ
  cost≡cost/tele : ∀ l q → cost/seq/tele l q ≡ (ϕ/-1 l q Int.⊖ ϕ/0 l q) Int.+ (Int.+ (cost/seq l q))
  cost≡cost/tele [] q =
    P.sym
    (
      begin
      (ϕ q Int.⊖ ϕ q) Int.+ (Int.+ 0) ≡⟨ IntP.+-identityʳ (ϕ q Int.⊖ ϕ q) ⟩
      ϕ q Int.⊖ ϕ q ≡⟨ IntP.n⊖n≡0 (ϕ q) ⟩
      Int.+ 0 ≡⟨ refl ⟩
      Int.+ 0
      ∎
    )
    where open ≡-Reasoning
  cost≡cost/tele (o ∷ os) q rewrite operateϕ≡ϕ∘operate o q
                                  | bind/meta Q ℕ Int.ℤ
                                    (o operate q)
                                    (λ q' → op/cost o q + cost/seq os q')
                                    (λ x → (ϕ/-1 (o ∷ os) q Int.⊖ ϕ/0 (o ∷ os) q) Int.+ (Int.+ x))
                                  | bind/dup Q ℕ Int.ℤ (o operate q) (ϕ/-1 os) (λ q' x → (x Int.⊖ ϕ q) Int.+ (Int.+ (op/cost o q + cost/seq os q')))
                                  | bind/dup Q ℕ Int.ℤ (o operate q) ϕ (λ q' x → Int.+ (op/cost o q) Int.+ (x Int.⊖ ϕ q) Int.+ (cost/seq/tele os q')) =
    P.cong (λ f → bind (meta Int.ℤ) (o operate q) f)
    (funext (λ q' →
    (
      begin
      (Int.+ (op/cost o q)) Int.+ (ϕ q' Int.⊖ ϕ q) Int.+ (cost/seq/tele os q') ≡⟨ P.cong (λ x → (Int.+ (op/cost o q)) Int.+ (ϕ q' Int.⊖ ϕ q) Int.+ x) (cost≡cost/tele os q') ⟩
      Int.+ op/cost o q Int.+ (ϕ q' Int.⊖ ϕ q) Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → x Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ Int.+ cost/seq os q')) (IntP.+-comm (Int.+ op/cost o q) (ϕ q' Int.⊖ ϕ q)) ⟩
      ϕ q' Int.⊖ ϕ q Int.+ Int.+ op/cost o q Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ Int.+ cost/seq os q') ≡⟨ IntP.+-assoc (ϕ q' Int.⊖ ϕ q) (Int.+ op/cost o q) (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ Int.+ cost/seq os q') ⟩
      ϕ q' Int.⊖ ϕ q Int.+ (Int.+ op/cost o q Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ Int.+ cost/seq os q')) ≡⟨ P.cong (λ x → ϕ q' Int.⊖ ϕ q Int.+ x) (P.sym (IntP.+-assoc (Int.+ op/cost o q) (ϕ/-1 os q' Int.⊖ ϕ/0 os q') (Int.+ cost/seq os q'))) ⟩
      ϕ q' Int.⊖ ϕ q Int.+ (Int.+ op/cost o q Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q') Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → ϕ q' Int.⊖ ϕ q Int.+ (x Int.+ Int.+ cost/seq os q')) (IntP.+-comm (Int.+ op/cost o q) (ϕ/-1 os q' Int.⊖ ϕ/0 os q')) ⟩
      ϕ q' Int.⊖ ϕ q Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → ϕ q' Int.⊖ ϕ q Int.+ x) (IntP.+-assoc (ϕ/-1 os q' Int.⊖ ϕ/0 os q') (Int.+ op/cost o q) (Int.+ cost/seq os q')) ⟩
      ϕ q' Int.⊖ ϕ q Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q' Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) ≡⟨ P.sym (IntP.+-assoc (ϕ q' Int.⊖ ϕ q) (ϕ/-1 os q' Int.⊖ ϕ/0 os q') (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) ⟩
      ϕ q' Int.⊖ ϕ q Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q') Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → x Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q') Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) (P.sym (IntP.m-n≡m⊖n (ϕ q') (ϕ q))) ⟩
      Int.+ ϕ q' Int.- (Int.+ ϕ q) Int.+ (ϕ/-1 os q' Int.⊖ ϕ/0 os q') Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → Int.+ ϕ q' Int.- (Int.+ ϕ q) Int.+ x Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) (P.sym (IntP.m-n≡m⊖n (ϕ/-1 os q') (ϕ/0 os q'))) ⟩
      Int.+ ϕ q' Int.- Int.+ ϕ q Int.+ (Int.+ ϕ/-1 os q' Int.- (Int.+ ϕ/0 os q')) Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → x Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) (IntP.+-comm (Int.+ ϕ q' Int.- Int.+ ϕ q) (Int.+ ϕ/-1 os q' Int.- (Int.+ ϕ/0 os q'))) ⟩
      Int.+ ϕ/-1 os q' Int.- Int.+ ϕ/0 os q' Int.+ (Int.+ ϕ q' Int.- Int.+ ϕ q) Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → x Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) (IntP.+-minus-telescope (Int.+ ϕ/-1 os q') (Int.+ ϕ q') (Int.+ ϕ q)) ⟩
      Int.+ ϕ/-1 os q' Int.- Int.+ ϕ q Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ P.cong (λ x → x Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')) (IntP.m-n≡m⊖n (ϕ/-1 os q') (ϕ q )) ⟩
      ϕ/-1 os q' Int.⊖ ϕ q Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q') ≡⟨ refl ⟩
      ϕ/-1 os q' Int.⊖ ϕ q Int.+ (Int.+ op/cost o q Int.+ Int.+ cost/seq os q')
      ∎
    )
    ))
    where open ≡-Reasoning

  data Amortized : List op → List ℕ → Set where
    a/emp : Amortized [] []
    a/cons : ∀ o k l l' → is/acost o k → Amortized l l' → Amortized (o ∷ l) (k ∷ l')

  amortized≥cost/tele : ∀ q0 l l' → Amortized l l' → Int.+ (lsum l') Int.≥ cost/seq/tele l q0
  amortized≥cost/tele q .[] .[] a/emp = IntP.≤-refl
  amortized≥cost/tele q .(o ∷ os) .(k ∷ l') (a/cons o k os l' x h) rewrite tbind/meta Q Int.ℤ (o operate q) (λ q' → (Int.+ (op/cost o q)) Int.+ (o operateϕ q Int.⊖ ϕ q) Int.+ (cost/seq/tele os q')) (λ z → z Int.≤ Int.+ lsum (k ∷ l')) =
    dbind (λ q' → meta ((Int.+ (op/cost o q)) Int.+ (o operateϕ q Int.⊖ ϕ q) Int.+ (cost/seq/tele os q') Int.≤ Int.+ lsum (k ∷ l'))) (o operate q)
    λ q' →
    begin
    Int.+ op/cost o q Int.+ ((o operateϕ q) Int.⊖ ϕ q) Int.+ cost/seq/tele os q' ≤⟨ IntP.+-monoˡ-≤ (cost/seq/tele os q') (x q) ⟩
    Int.+ k Int.+ cost/seq/tele os q' ≤⟨ IntP.+-monoʳ-≤ (Int.+ k) (amortized≥cost/tele q' os l' h) ⟩
    Int.+ k Int.+ Int.+ lsum l' ≤⟨ IntP.≤-refl ⟩
    Int.+ k Int.+ Int.+ lsum l'
    ∎
   where open IntP.≤-Reasoning

  -- Sum of a sequence of amortized costs (plus the initial potential) bounds the sum of the sequence of actual costs
  amortized≥cost : ∀ q l l' → Amortized l l' → Int.+ (ϕ q + lsum l') Int.≥ Int.+ (cost/seq l q)
  amortized≥cost q l l' h =
    begin
    Int.+ (cost/seq l q) ≤⟨ IntP.n≤m+n (0 + ϕ/-1 l q) ⟩
    Int.0ℤ Int.+ (Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → x Int.+ (Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q) (P.sym (IntP.n⊖n≡0 (ϕ q))) ⟩
    ϕ q Int.⊖ ϕ q Int.+ Int.+ ϕ/-1 l q Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → x Int.+ (Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q) (P.sym (IntP.m-n≡m⊖n (ϕ q) (ϕ q))) ⟩
    Int.+ ϕ q Int.+ Int.- (Int.+ ϕ q) Int.+ Int.+ ϕ/-1 l q Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → x Int.+ Int.+ cost/seq l q) (IntP.+-assoc (Int.+ ϕ q) (Int.- (Int.+ ϕ q)) (Int.+ ϕ/-1 l q)) ⟩
    Int.+ ϕ q Int.+ (Int.- (Int.+ ϕ q) Int.+ Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → Int.+ ϕ q Int.+ x Int.+ Int.+ cost/seq l q) (IntP.+-comm (Int.- (Int.+ ϕ q)) (Int.+ ϕ/-1 l q)) ⟩
    Int.+ ϕ q Int.+ (Int.+ ϕ/-1 l q Int.- (Int.+ ϕ q)) Int.+ Int.+ cost/seq l q ≡⟨ IntP.+-assoc (Int.+ ϕ q) (Int.+ ϕ/-1 l q Int.- (Int.+ ϕ q)) (Int.+ cost/seq l q) ⟩
    Int.+ ϕ q Int.+ (Int.+ ϕ/-1 l q Int.- Int.+ ϕ q Int.+ Int.+ cost/seq l q) ≡⟨ P.cong (λ x → Int.+ ϕ q Int.+ (x Int.+ Int.+ cost/seq l q)) (IntP.m-n≡m⊖n (ϕ/-1 l q) (ϕ q)) ⟩
    Int.+ ϕ q Int.+ (ϕ/-1 l q Int.⊖ ϕ q Int.+ Int.+ cost/seq l q) ≡⟨ P.cong (λ x → Int.+ ϕ q Int.+ x) (P.sym (cost≡cost/tele l q)) ⟩
    Int.+ ϕ q Int.+ cost/seq/tele l q ≤⟨ IntP.+-monoʳ-≤ (Int.+ ϕ q) (amortized≥cost/tele q l l' h) ⟩
    Int.+ ϕ q Int.+ Int.+ lsum l' ≤⟨ IntP.≤-refl ⟩
    Int.+ ϕ q Int.+ Int.+ lsum l'
    ∎
   where open IntP.≤-Reasoning

  -- Amortized cost for enq and deq on a front-back queue
  enq/acost : ∀ x → is/acost (op/enq x) 2
  enq/acost x (f , b)  =
    begin
    Int.0ℤ Int.+ ((len f + 2 * (1 + len b)) Int.⊖ (ϕ (f , b))) ≡⟨ IntP.+-identityˡ ((len f + 2 * (len (cons x b))) Int.⊖ (ϕ (f , b))) ⟩
    len f + 2 * len (cons x b) Int.⊖ ϕ (f , b) ≡⟨ P.cong (λ x → (len f + x) Int.⊖ (ϕ (f , b))) (*-distribˡ-+ 2 1 (len b)) ⟩
    len f + (2 * 1 + 2 * len b) Int.⊖ ϕ (f , b) ≡⟨ P.cong (λ x → (len f + x) Int.⊖ (ϕ (f , b)) ) (+-comm 2 (2 * len b)) ⟩
    len f + (2 * len b + 2) Int.⊖ ϕ (f , b) ≡⟨ P.cong (λ x → x Int.⊖ (ϕ (f , b))) (P.sym (+-assoc (len f) (2 * len b) 2)) ⟩
    len f + 2 * len b + 2 Int.⊖ ϕ (f , b) ≡⟨ P.cong (λ x → (len f + 2 * len b + 2) Int.⊖ x) (P.sym (+-identityʳ (ϕ (f , b)))) ⟩
    len f + 2 * len b + 2 Int.⊖ (ϕ (f , b) + 0) ≡⟨ IntP.+-cancelˡ-⊖ (len f + 2 * len b) 2 0 ⟩
    (Int.+ 2) ≤⟨ IntP.≤-refl ⟩
    Int.+ 2
    ∎
    where open IntP.≤-Reasoning

  n+n≡2*n : ∀ n → n + n ≡ 2 * n
  n+n≡2*n n =
    begin
    n + n ≡⟨ P.cong (λ x → n + x) (P.sym (+-identityʳ n)) ⟩
    2 * n ∎
    where open ≡-Reasoning

  deq/acost : is/acost op/deq 0
  deq/acost (f , b) =
    list/match f (λ f → meta ((Int.+ (op/cost op/deq (f , b))) Int.+ ((op/deq operateϕ (f , b)) Int.⊖ (ϕ (f , b))) Int.≤ Int.0ℤ))
    (
    list/match b (λ b → meta ((Int.+ (op/cost op/deq (nil , b))) Int.+ ((op/deq operateϕ (nil , b)) Int.⊖ (ϕ (nil , b))) Int.≤ Int.0ℤ))
    IntP.≤-refl
    λ a b' →
    begin
    Int.+ (2 + len b') Int.+ (len b' Int.⊖ (2 * (1 + len b'))) ≡⟨ IntP.distribʳ-⊖-+-pos (2 + len b') (len b') (2 * (1 + len b')) ⟩
    2 + len b' + len b' Int.⊖ 2 * (1 + len b') ≡⟨ P.cong (λ x → x Int.⊖ 2 * (1 + len b')) (+-assoc 2 (len b') (len b')) ⟩
    2 + (len b' + len b') Int.⊖ 2 * (1 + len b') ≡⟨ P.cong (λ x → 2 + (len b'  + len b') Int.⊖ x) (*-distribˡ-+ 2 1 (len b')) ⟩
    2 + (len b' + len b') Int.⊖ (2 * 1 + 2 * len b') ≡⟨ P.cong (λ x → 2 + x Int.⊖ (2 + 2 * len b')) (n+n≡2*n (len b')) ⟩
    2 + 2 * len b' Int.⊖ (2 + 2 * len b') ≡⟨ IntP.n⊖n≡0 (2 + 2 * len b') ⟩
    Int.0ℤ ≤⟨ IntP.≤-refl ⟩
    Int.0ℤ
    ∎
    )
    λ a f' →
    begin
    Int.+ 1 Int.+ ((len f' + 2 * len b) Int.⊖ (1 + len f' + 2 * len b)) ≡⟨ IntP.distribʳ-⊖-+-pos 1 (len f' + 2 * len b) (1 + len f' + 2 * len b) ⟩
    1 + (len f' + 2 * len b) Int.⊖ (1 + len f' + 2 * len b) ≡⟨ P.cong (λ x → x Int.⊖ (1 + len f' + 2 * len b)) (P.sym (+-assoc 1 (len f') (2 * len b))) ⟩
    1 + len f' + 2 * len b Int.⊖ (1 + len f' + 2 * len b) ≡⟨ IntP.n⊖n≡0 (1 + len f' + 2 * len b) ⟩
    Int.0ℤ ≤⟨ IntP.≤-refl ⟩
    Int.0ℤ
    ∎
    where open IntP.≤-Reasoning

  all2s : ℕ → List ℕ
  all2s n = tabulate {n = n} (λ _ → 2)

  sum2s : ∀ n → lsum (all2s n) ≡ 2 * n
  sum2s zero = refl
  sum2s (suc n) =
    begin
    2 + lsum (all2s n) ≡⟨ P.cong (λ x → 2 + x) (sum2s n) ⟩
    2 + 2 * n ≡⟨ P.cong (λ x → x + 2 * n) (*-identityʳ 2) ⟩
    2 * 1 + 2 * n ≡⟨ P.sym (*-distribˡ-+ 2 1 n) ⟩
    2 * (1 + n) ≡⟨ refl ⟩
    2 * (1 + n)
    ∎
   where open ≡-Reasoning

  all2s/is/acost : ∀ l → Amortized l (all2s (length l))
  all2s/is/acost [] = a/emp
  all2s/is/acost ((op/enq x) ∷ os) = a/cons (op/enq x) 2 os (all2s (length os)) (enq/acost x) (all2s/is/acost os)
  all2s/is/acost (op/deq ∷ os) = a/cons op/deq 2 os (all2s (length os)) (acost/weaken z≤n deq/acost) (all2s/is/acost os)

  fb/amortized : ∀ q l → Int.+ (cost/seq l q) Int.≤  Int.+ (ϕ q + 2 * length l)
  fb/amortized q l =
    begin
    Int.+ (cost/seq l q) ≤⟨ amortized≥cost q l (all2s (length l)) (all2s/is/acost l) ⟩
    Int.+ (ϕ q + lsum (all2s (length l))) ≡⟨ P.cong (λ x → Int.+ (ϕ q + x)) (sum2s (length l)) ⟩
    Int.+ (ϕ q + 2 * length l) ≤⟨ IntP.≤-refl ⟩
    Int.+ (ϕ q + 2 * length l)
    ∎
   where open IntP.≤-Reasoning

  -- Starting with an empty queue, a sequence of n operations costs at most 2 * n
  fb≤2*|l| : ∀ l → ub Q (l operate/seq emp) (2 * length l)
  fb≤2*|l| l = ub/relax (IntP.drop‿+≤+ (fb/amortized emp l)) (operate/seq≤cost/seq l emp)
