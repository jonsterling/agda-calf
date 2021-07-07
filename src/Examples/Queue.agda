{-# OPTIONS --prop --rewriting #-}

module Examples.Queue where

open import Calf.CostMonoid
open import Calf.CostMonoids using (ℕ-CostMonoid)

costMonoid = ℕ-CostMonoid
open CostMonoid costMonoid using (ℂ)

open import Calf costMonoid
open import Calf.Types.Nat
open import Calf.Types.Unit
open import Calf.Types.Sum

open import Function
open import Data.Nat
open import Data.Nat.Properties
import Data.Integer as Int
import Data.Integer.Properties as IntP
open import Data.List renaming (sum to lsum)
open import Data.Product
open import Relation.Binary.PropositionalEquality as P

record Queue (A : tp pos) : Set where
  field
    Q : tp pos
    emp : val Q
    enq : cmp (Π Q λ _ → Π A λ _ → F Q)
    deq : cmp (Π Q λ _ → F (sum unit (Σ++ Q λ _ → A)))

module CostList (A : tp pos) (n : ℕ) where
  -- Suppose we want to implement the Queue signature above using lists.
  -- One cost model is to count the number of times a cons node is inspected.
  -- This is implemented by the following annotated list type:
  -- destructing a cons node of type list n A consumes n steps.
  postulate
    list : tp pos
    nil : val list
    cons : val A → val list → val list

    list/ind : (l : val list) → (X : val list → tp neg) → cmp (X nil) →
      ((a : val A) → (l : val list) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      cmp (X l)
    list/ind/nil : ∀ {X} → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val list) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      list/ind nil X e0 e1 ≡ e0
    {-# REWRITE list/ind/nil #-}
    list/ind/cons : ∀ {X} → (a : val A) → (l : val list) → (e0 : cmp (X nil)) →
        (e1 : (a : val A) → (l : val list) → (r : val (U (X l))) →
        cmp (X (cons a l))) →
      list/ind (cons a l) X e0 e1 ≡ step (X (cons a l)) n (e1 a l (list/ind l X e0 e1))
    {-# REWRITE list/ind/cons #-}

  list/match : (l : val list) → (X : val list → tp neg) → cmp (X nil) →
    ((a : val A) → (l : val list) → cmp (X (cons a l))) →
    cmp (X l)
  list/match l X e0 e1 = list/ind l X e0 (λ a l _ → e1 a l)

  bound/list/match : ∀ (l : val list) (X : val list → tp pos)
    {e0 : val (U (F (X nil)))} {e1 : (a : val A) → (l : val list) → val (U (F (X (cons a l))))}
    {p0 : val (U cost)} {p1 : (a : val A) → (l : val list) → val (U cost)} →
    IsBounded (X nil) e0 p0 →
    ((a : val A) → (l : val list) → IsBounded (X (cons a l)) (e1 a l) (p1 a l)) →
    IsBounded (X l) (list/match l (F ∘ X) e0 e1) (list/match l (λ _ → cost) p0 (λ a l → n + p1 a l))
  bound/list/match l X {e0} {e1} {p0} {p1} ub0 ub1 =
    list/match l (λ l → meta (IsBounded (X l) (list/match l (F ∘ X) e0 e1) (list/match l (λ _ → cost) p0 (λ a l → n + p1 a l))))
      ub0
      λ a l → bound/circ n (bound/step n (p1 a l) (ub1 a l))

  len : val list → ℕ
  len l = list/ind l (λ _ → meta ℕ) 0 λ a l r → 1 + r

module Ex/CostList where
  open CostList nat 0

  ex : val list
  ex = cons 0 (cons 1 nil)

module Rev (A : tp pos) where
  open CostList A 1

  revAppend : cmp (Π list λ _ → Π list λ _ → F list)
  revAppend l =
    list/ind l (λ _ → Π list λ _ → F list)
      (λ l' → ret l')
      λ x _ r → λ l' → r (cons x l')

  revAppend/lemma/cons : ∀ x xs l' → ◯ (∃ λ y → ∃ λ ys → (len ys ≡ len xs + len l') × revAppend (cons x xs) l' ≡ ret (cons y ys))
  revAppend/lemma/cons x xs =
    list/ind xs (λ xs → meta (∀ x l' → ◯ (∃ λ y → ∃ λ ys → (len ys ≡ len xs + len l') × revAppend (cons x xs) l' ≡ ret (cons y ys))))
      (λ x l' u → (x , l' , refl , step/ext (F list) (ret (cons x l')) 1 u))
      (λ x' xs' ih x l' u →
        let (y , ys , h , ≡) = ih x' (cons x l') u in
        let open ≡-Reasoning in
        y , ys , (
          begin
            len ys
          ≡⟨ h ⟩
            len xs' + len (cons x l')
          ≡⟨⟩
            len xs' + step (meta ℕ) 1 (suc (len l'))
          ≡⟨ cong (len xs' +_) (step/ext (meta ℕ) (suc (len l')) 1 u) ⟩
            len xs' + suc (len l')
          ≡⟨ +-suc (len xs') (len l') ⟩
            suc (len xs' + len l')
          ≡⟨⟩
            suc (len xs') + len l'
          ≡˘⟨ cong (_+ len l') (step/ext (meta ℕ) (suc (len xs')) 1 u) ⟩
            step (meta ℕ) 1 (suc (len xs')) + len l'
          ≡⟨⟩
            len (cons x' xs') + len l'
          ∎
        ) , (
          begin
            revAppend (cons x (cons x' xs')) l'
          ≡⟨⟩
            step (F list) 1 (revAppend (cons x' xs') (cons x l'))
          ≡⟨ step/ext (F list) _ 1 u ⟩
            revAppend (cons x' xs') (cons x l')
          ≡⟨ (≡) ⟩
            ret (cons y ys)
          ∎
        ))
      x

  revAppend/cost : cmp (Π list λ _ → Π list λ _ → cost)
  revAppend/cost l l' = len l

  revAppend≤revAppend/cost : ∀ l l' → IsBounded list (revAppend l l') (revAppend/cost l l')
  revAppend≤revAppend/cost l =
    list/ind l (λ l → meta (∀ l' → IsBounded list (revAppend l l') (revAppend/cost l l')))
      (λ l' → bound/ret)
      (λ a l r → λ l' → bound/circ 1 (bound/step 1 (len l) (r (cons a l'))))

  rev : cmp (Π list λ _ → F list)
  rev l = revAppend l nil

  rev/lemma/cons : ∀ x xs → ◯ (∃ λ y → ∃ λ ys → len ys ≡ len xs × rev (cons x xs) ≡ ret (cons y ys))
  rev/lemma/cons x xs =
    subst (λ n → ◯ (∃ λ y → ∃ λ ys → len ys ≡ n × rev (cons x xs) ≡ ret (cons y ys)))
      (+-identityʳ _)
      (revAppend/lemma/cons x xs nil)

  rev/cost : cmp (Π list λ _ → cost)
  rev/cost l = len l

  rev≤rev/cost : ∀ l → IsBounded list (rev l) (rev/cost l)
  rev≤rev/cost l = revAppend≤revAppend/cost l nil


-- Implement Queue with a pair of lists; (f , b) represents the queue f :: rev b.
module FrontBack (A : tp pos) where
  -- For simplicity, we charge 1 step for each cons node destruction.
  open CostList A 1
  open Rev A

  Q : tp pos
  Q = Σ++ list λ _ → list

  emp : val Q
  emp = (nil , nil)

  enq : cmp (Π Q λ _ → Π A λ _ → F Q)
  enq (f , b) x = ret (f , cons x b)

  enq/cost : cmp (Π Q λ _ → Π A λ _ → cost)
  enq/cost (f , b) x = 0

  enq≤enq/cost : ∀ q x → IsBounded Q (enq q x) (enq/cost q x)
  enq≤enq/cost q x = bound/ret

  deq-tp = sum unit (Σ++ Q λ _ → A)

  deq/emp : cmp (Π list λ _ → F deq-tp)
  deq/emp l =
    list/match l (λ _ → F deq-tp)
      (ret (inj₁ triv))
      λ a l' → ret (inj₂ ((l' , nil) , a))

  deq/emp/cost : cmp (Π list λ _ → cost)
  deq/emp/cost l =
    list/match l (λ _ → cost)
      0
      λ a l' → 1 + 0

  deq/emp≤deq/emp/cost : ∀ l → IsBounded deq-tp (deq/emp l) (deq/emp/cost l)
  deq/emp≤deq/emp/cost l =
    bound/list/match l (λ _ → deq-tp)
      bound/ret
      λ a l' → bound/ret

  deq : cmp (Π Q λ _ → F deq-tp)
  deq (f , b) =
    list/match f (λ _ → F deq-tp)
      (bind (F deq-tp) (rev b) (λ b' → deq/emp b'))
      λ a l → ret (inj₂ ((l , b) , a))

  deq/cost : cmp (Π Q λ _ → cost)
  deq/cost (f , b) =
    list/match f (λ _ → cost)
      (bind cost (rev b) (λ b' → rev/cost b + deq/emp/cost b'))
      λ a l → 1 + 0

  deq/cost/closed : cmp (Π Q λ _ → cost)
  deq/cost/closed (f , b) =
    list/match f (λ _ → cost)
      (list/match b (λ _ → cost) 0 (λ _ b' → 1 + len b))
      λ _ _ → 1

  deq/cost≤deq/cost/closed : ∀ q → ◯ (deq/cost q ≤ deq/cost/closed q)
  deq/cost≤deq/cost/closed (f , b) u =
    list/match f (λ f → meta (deq/cost (f , b) ≤ deq/cost/closed (f , b)))
      (list/match b (λ b → meta (deq/cost (nil , b) ≤ deq/cost/closed (nil , b)))
        ≤-refl
        λ x xs →
          let open ≤-Reasoning in
          let (y , ys , _ , ≡) = rev/lemma/cons x xs u in
          begin
            deq/cost (nil , cons x xs)
          ≡⟨⟩
            bind cost (rev (cons x xs)) (λ b' → rev/cost (cons x xs) + deq/emp/cost b')
          ≡⟨⟩
            bind cost (rev (cons x xs)) (λ b' → rev/cost (cons x xs) + deq/emp/cost b')
          ≡⟨ cong (λ e → bind cost e (λ b' → rev/cost (cons x xs) + deq/emp/cost b')) (≡) ⟩
            rev/cost (cons x xs) + deq/emp/cost (cons y ys)
          ≡⟨⟩
            step cost 1 (suc (len xs)) + step cost 1 1
          ≡⟨ cong₂ _+_ (step/ext cost (suc (len xs)) 1 u) (step/ext cost 1 1 u) ⟩
            suc (len xs) + 1
          ≡⟨ +-comm (suc (len xs)) 1 ⟩
            suc (suc (len xs))
          ≡˘⟨ cong suc (step/ext cost _ 1 u) ⟩
            suc (step cost 1 (suc (len xs)))
          ≡⟨⟩
            suc (len (cons x xs))
          ≡˘⟨ step/ext cost _ 1 u ⟩
            step cost 1 (suc (len (cons x xs)))
          ≡⟨⟩
            list/match (cons x xs) (λ _ → cost) 0 (λ _ b' → 1 + len (cons x xs))
          ≡⟨⟩
            deq/cost/closed (nil , cons x xs)
          ∎
      )
      λ _ _ → ≤-refl

  deq≤deq/cost : ∀ q → IsBounded deq-tp (deq q) (deq/cost q)
  deq≤deq/cost (f , b) =
    bound/list/match f (λ _ → deq-tp)
      (bound/bind (rev/cost b) _ (rev≤rev/cost b) λ b' → deq/emp≤deq/emp/cost b')
      λ a l → bound/ret

  deq≤deq/cost/closed : ∀ q → IsBounded deq-tp (deq q) (deq/cost/closed q)
  deq≤deq/cost/closed q = bound/relax (deq/cost≤deq/cost/closed q) (deq≤deq/cost q)

  -- Amortized analysis for front-back queue.
  -- The goal is to bound the cost of a single-thread sequence of queue operations staring with an initial queue q0,
  -- where an operation is either an enqueue or a dequeue.
  data op : Set where
    op/enq : (x : val A) → op
    op/deq : op

  -- Potential function
  ϕ : val Q → ℕ
  ϕ (f , b) = len f + 2 * len b

  -- o operate q is the computation induced by operation o on queue q.
  -- Needed because deq doesn't always return a queue (e.g., deq emp).
  -- In these cases we just return the empty queue.
  _operate_ : op → val Q → cmp (F Q)
  (op/enq x) operate q = enq q x
  (op/deq) operate q =
    bind (F Q) (deq q) λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s
    (λ _ → ret (nil , nil))
    (λ (q , x) → ret q))

  -- o operateϕ q is morally ϕ (o operate q), which doesn't type-check since o operate q is a computation.
  -- Easier to work with than bind cost (o operate q) ϕ (but they are equivalent, as shown below).
  _operateϕ_ : op → val Q → ℂ
  (op/enq x) operateϕ (f , b) = len f + 2 * (1 + len b)
  (op/deq) operateϕ (f , b) = list/match f (λ _ → cost) (list/match b (λ _ → cost) 0 (λ _ b' → len b')) (λ _ f' → len f' + 2 * len b)

  operateϕ≡ϕ∘operate : ∀ o q → ◯ (o operateϕ q ≡ bind cost (o operate q) ϕ)
  operateϕ≡ϕ∘operate (op/enq x) (f , b) u =
    begin
      len f + 2 * (1 + len b)
    ≡˘⟨ cong (λ n → len f + 2 * n) (step/ext cost (1 + len b) 1 u) ⟩
      len f + 2 * step cost 1 (1 + len b)
    ≡⟨⟩
      bind cost (enq (f , b) x) ϕ
    ∎
      where open ≡-Reasoning
  operateϕ≡ϕ∘operate op/deq (f , b) u = list/match f
        (λ f →
          meta
          ((op/deq operateϕ (f , b)) ≡
            bind cost (op/deq operate (f , b)) ϕ))
        (list/ind b (λ b → meta ((op/deq operateϕ (nil , b)) ≡ bind cost (op/deq operate (nil , b)) ϕ))
        refl
        λ a l ih → emp/cons a l)
        λ a l → refl

    where
    emp/cons : ∀ a l → op/deq operateϕ (nil , cons a l) ≡ bind cost (op/deq operate (nil , cons a l)) ϕ
    emp/cons a l with rev/lemma/cons a l u
    ... | (x' , l' , eqn1 , eqn2) =
      begin
        op/deq operateϕ (nil , cons a l)
      ≡⟨⟩
        step cost 1 (len l)
      ≡⟨ step/ext cost (len l) 1 u ⟩
        len l
      ≡⟨ P.sym eqn1 ⟩
        len l'
      ≡⟨ P.sym (+-identityʳ (len l')) ⟩
        len l' + 0
      ≡⟨⟩
        len l' + 2 * len nil
      ≡⟨⟩
        ϕ (l' , nil)
      ≡˘⟨ step/ext cost (ϕ (l' , nil)) 1 u ⟩
        step cost 1 (ϕ (l' , nil))
      ≡⟨⟩
        bind cost
          (step (F Q) 1 (ret (l' , nil)))
          ϕ
      ≡⟨⟩
        bind cost
          (bind (F Q) (step (F deq-tp) 1 (ret (inj₂ ((l' , nil) , x')))) λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s
            (λ _ → ret (nil , nil))
            (λ (q , x) → ret q)))
          ϕ
      ≡⟨⟩
        bind cost
          (bind (F Q) (deq/emp (cons x' l')) λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s
            (λ _ → ret (nil , nil))
            (λ (q , x) → ret q)))
          ϕ
      ≡˘⟨
        cong
          (λ e →
            bind cost
              (bind (F Q) e λ l' →
                bind (F Q) (deq/emp l') λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s
                  (λ _ → ret (nil , nil))
                  (λ (q , x) → ret q)))
              ϕ
          )
          eqn2
      ⟩
        bind cost
          (bind (F Q) (rev (cons a l)) λ l' →
            bind (F Q) (deq/emp l') λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s
              (λ _ → ret (nil , nil))
              (λ (q , x) → ret q)))
          ϕ
      ≡⟨⟩
        bind cost
          (bind (F Q) (deq (nil , cons a l)) λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s
            (λ _ → ret (nil , nil))
            (λ (q , x) → ret q)))
          ϕ
      ≡⟨⟩
        bind cost (op/deq operate (nil , cons a l)) ϕ
      ∎
      where open ≡-Reasoning

  -- op/cost o q is the cost of o operate q.
  op/cost : op → val Q → ℕ
  op/cost (op/enq x) q = 0
  op/cost (op/deq) (f , b) = list/match f (λ _ → cost) (list/match b (λ _ → cost) 0 (λ _ b' → 2 + len b')) (λ _ _ → 1)

  deq/cost≡cost/deq : ∀ q → ◯ (deq/cost/closed q ≡ op/cost op/deq q)
  deq/cost≡cost/deq (f , b) u =
    P.cong (λ x → list/match f (λ _ → cost) x (λ _ _ → 1)) (
      list/match b
        (λ b →
          meta
            (list/match b (λ _ → cost) 0 (λ _ b' → 1 + len b) ≡
              list/match b (λ _ → cost) 0 (λ _ b' → 2 + len b')))
        refl
        (λ a l →
          let open ≡-Reasoning in
          begin
            list/match (cons a l) (λ _ → cost) 0 (λ _ b' → 1 + len (cons a l))
          ≡⟨⟩
            step cost 1 (1 + len (cons a l))
          ≡⟨ step/ext cost (1 + len (cons a l)) 1 u ⟩
            1 + len (cons a l)
          ≡⟨⟩
            1 + step cost 1 (suc (len l))
          ≡⟨ cong (1 +_) (step/ext cost (suc (len l)) 1 u) ⟩
            2 + len l
          ≡˘⟨ step/ext cost (2 + len l) 1 u ⟩
            step cost 1 (2 + len l)
          ≡⟨⟩
            list/match (cons a l) (λ _ → cost) 0 (λ _ b' → 2 + len b')
          ∎
        )
    )

  -- cost o q upperbounds the cost of o operate q.
  op≤cost : ∀ o q → IsBounded Q (o operate q) (op/cost o q)
  op≤cost (op/enq x) q = enq≤enq/cost q x
  op≤cost op/deq q rewrite P.sym (+-identityʳ (op/cost (op/deq) q)) =
    bound/bind/const {A = deq-tp} {e = deq q} {f = λ s → (sum/case unit (Σ++ Q λ _ → A) (λ _ → F Q) s (λ _ → ret (nil , nil)) (λ (q , x) → ret q))}
      (op/cost op/deq q) 0
      (bound/relax (λ u → ≤-reflexive (deq/cost≡cost/deq q u)) (deq≤deq/cost/closed q))
      λ a →
        bound/sum/case/const/const unit ((Σ++ Q λ _ → A)) (λ _ → Q) a ((λ _ → ret (nil , nil))) (λ (q , x) → ret q) 0
          (λ _ → bound/ret)
          (λ _ → bound/ret)

  -- is/acost o k when for any state q, k suffices for the cost of o on q and the difference in the potential.
  is/acost :  op → ℕ → Set
  is/acost o k = ∀ q → (Int.+ (op/cost o q)) Int.+ ((o operateϕ q) Int.⊖ (ϕ q)) Int.≤ Int.+ k

  acost/weaken : ∀ {m n o} → m ≤ n → is/acost o m → is/acost o n
  acost/weaken h1 h2 = λ q → IntP.≤-trans (h2 q) (Int.+≤+ h1)

  -- A sequence of operations induces a single computation by threading through the initial state q0.
  _operate/seq_ : List op → val Q → cmp (F Q)
  [] operate/seq q0 = ret q0
  (o ∷ os) operate/seq q = bind (F Q) (o operate q) λ q' → os operate/seq q'

  cost/seq : ∀ (l : List op) → val Q → ℂ
  cost/seq [] q0 = 0
  cost/seq (o ∷ os) q = bind cost (o operate q) λ q' → op/cost o q + cost/seq os q'

  -- Cost of a sequence computation is bounded by the sum of cost of the constituents.
  operate/seq≤cost/seq : ∀ l q → IsBounded Q (l operate/seq q) (cost/seq l q)
  operate/seq≤cost/seq [] q0 = bound/ret
  operate/seq≤cost/seq (o ∷ os) q = bound/bind {A = Q} {e = o operate q} {f = λ q → os operate/seq q}
   (op/cost o q) (cost/seq os) (op≤cost o q) λ q → operate/seq≤cost/seq os q

  -- Telescoping the potential.
  cost/seq/tele : ∀ (l : List op) → val Q → Int.ℤ
  cost/seq/tele [] q0 = Int.0ℤ
  cost/seq/tele (o ∷ os) q = bind (meta Int.ℤ) (o operate q) λ q' → (Int.+ (op/cost o q)) Int.+ (o operateϕ q Int.⊖ ϕ q) Int.+ (cost/seq/tele os q')

  ϕn : ℕ → List op → val Q → ℕ
  ϕn zero l q0 = ϕ q0
  ϕn (suc n) (o ∷ os) q = bind cost (o operate q) λ q' → ϕn n os q'
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
  cost≡cost/tele : ∀ l q → ◯ (cost/seq/tele l q ≡ (ϕ/-1 l q Int.⊖ ϕ/0 l q) Int.+ (Int.+ (cost/seq l q)))
  cost≡cost/tele [] q u =
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
  cost≡cost/tele (o ∷ os) q u rewrite operateϕ≡ϕ∘operate o q u
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
      (Int.+ (op/cost o q)) Int.+ (ϕ q' Int.⊖ ϕ q) Int.+ (cost/seq/tele os q') ≡⟨ P.cong (λ x → (Int.+ (op/cost o q)) Int.+ (ϕ q' Int.⊖ ϕ q) Int.+ x) (cost≡cost/tele os q' u) ⟩
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
  amortized≥cost : ∀ q l l' → Amortized l l' → ◯ (Int.+ (ϕ q + lsum l') Int.≥ Int.+ (cost/seq l q))
  amortized≥cost q l l' h u =
    begin
    Int.+ (cost/seq l q) ≤⟨ IntP.n≤m+n (0 + ϕ/-1 l q) ⟩
    Int.0ℤ Int.+ (Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → x Int.+ (Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q) (P.sym (IntP.n⊖n≡0 (ϕ q))) ⟩
    ϕ q Int.⊖ ϕ q Int.+ Int.+ ϕ/-1 l q Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → x Int.+ (Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q) (P.sym (IntP.m-n≡m⊖n (ϕ q) (ϕ q))) ⟩
    Int.+ ϕ q Int.+ Int.- (Int.+ ϕ q) Int.+ Int.+ ϕ/-1 l q Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → x Int.+ Int.+ cost/seq l q) (IntP.+-assoc (Int.+ ϕ q) (Int.- (Int.+ ϕ q)) (Int.+ ϕ/-1 l q)) ⟩
    Int.+ ϕ q Int.+ (Int.- (Int.+ ϕ q) Int.+ Int.+ ϕ/-1 l q) Int.+ Int.+ cost/seq l q ≡⟨ P.cong (λ x → Int.+ ϕ q Int.+ x Int.+ Int.+ cost/seq l q) (IntP.+-comm (Int.- (Int.+ ϕ q)) (Int.+ ϕ/-1 l q)) ⟩
    Int.+ ϕ q Int.+ (Int.+ ϕ/-1 l q Int.- (Int.+ ϕ q)) Int.+ Int.+ cost/seq l q ≡⟨ IntP.+-assoc (Int.+ ϕ q) (Int.+ ϕ/-1 l q Int.- (Int.+ ϕ q)) (Int.+ cost/seq l q) ⟩
    Int.+ ϕ q Int.+ (Int.+ ϕ/-1 l q Int.- Int.+ ϕ q Int.+ Int.+ cost/seq l q) ≡⟨ P.cong (λ x → Int.+ ϕ q Int.+ (x Int.+ Int.+ cost/seq l q)) (IntP.m-n≡m⊖n (ϕ/-1 l q) (ϕ q)) ⟩
    Int.+ ϕ q Int.+ (ϕ/-1 l q Int.⊖ ϕ q Int.+ Int.+ cost/seq l q) ≡⟨ P.cong (λ x → Int.+ ϕ q Int.+ x) (P.sym (cost≡cost/tele l q u)) ⟩
    Int.+ ϕ q Int.+ cost/seq/tele l q ≤⟨ IntP.+-monoʳ-≤ (Int.+ ϕ q) (amortized≥cost/tele q l l' h) ⟩
    Int.+ ϕ q Int.+ Int.+ lsum l' ≤⟨ IntP.≤-refl ⟩
    Int.+ ϕ q Int.+ Int.+ lsum l'
    ∎
   where open IntP.≤-Reasoning

  -- Amortized cost for enq and deq on a front-back queue
  enq/acost : ∀ x → ◯ (is/acost (op/enq x) 2)
  enq/acost x u (f , b) =
    begin
      (Int.+ (op/cost (op/enq x) (f , b))) Int.+ (((op/enq x) operateϕ (f , b)) Int.⊖ (ϕ (f , b)))
    ≡⟨⟩
      Int.0ℤ Int.+ ((len f + 2 * (1 + len b)) Int.⊖ (ϕ (f , b)))
    ≡⟨ IntP.+-identityˡ ((len f + 2 * (1 + len b)) Int.⊖ (ϕ (f , b))) ⟩
      len f + 2 * (1 + len b) Int.⊖ ϕ (f , b)
    ≡⟨ P.cong (λ x → (len f + x) Int.⊖ (ϕ (f , b))) (*-distribˡ-+ 2 1 (len b)) ⟩
      len f + (2 * 1 + 2 * len b) Int.⊖ ϕ (f , b)
    ≡⟨ P.cong (λ x → (len f + x) Int.⊖ (ϕ (f , b)) ) (+-comm 2 (2 * len b)) ⟩
      len f + (2 * len b + 2) Int.⊖ ϕ (f , b)
    ≡⟨ P.cong (λ x → x Int.⊖ (ϕ (f , b))) (P.sym (+-assoc (len f) (2 * len b) 2)) ⟩
      len f + 2 * len b + 2 Int.⊖ ϕ (f , b)
    ≡⟨ P.cong (λ x → (len f + 2 * len b + 2) Int.⊖ x) (P.sym (+-identityʳ (ϕ (f , b)))) ⟩
      len f + 2 * len b + 2 Int.⊖ (ϕ (f , b) + 0)
    ≡⟨ IntP.+-cancelˡ-⊖ (len f + 2 * len b) 2 0 ⟩
      Int.+ 2
    ∎
    where open IntP.≤-Reasoning

  n+n≡2*n : ∀ n → n + n ≡ 2 * n
  n+n≡2*n n =
    begin
    n + n ≡⟨ P.cong (λ x → n + x) (P.sym (+-identityʳ n)) ⟩
    2 * n ∎
    where open ≡-Reasoning

  deq/acost : ◯ (is/acost op/deq 0)
  deq/acost u (f , b) =
    list/match f (λ f → meta ((Int.+ (op/cost op/deq (f , b))) Int.+ ((op/deq operateϕ (f , b)) Int.⊖ (ϕ (f , b))) Int.≤ Int.0ℤ))
    (
    list/match b (λ b → meta ((Int.+ (op/cost op/deq (nil , b))) Int.+ ((op/deq operateϕ (nil , b)) Int.⊖ (ϕ (nil , b))) Int.≤ Int.0ℤ))
    IntP.≤-refl
    λ a b' →
      begin
        (Int.+ (op/cost op/deq (nil , cons a b'))) Int.+ ((op/deq operateϕ (nil , cons a b')) Int.⊖ (ϕ (nil , cons a b')))
      ≡⟨⟩
        Int.+ (step cost 1 (2 + len b')) Int.+ (step cost 1 (len b') Int.⊖ (2 * (step cost 1 (1 + len b'))))
      ≡⟨
        cong₂ Int._+_
          (cong Int.+_ (step/ext cost (2 + len b') 1 u))
          (cong₂ Int._⊖_
            (step/ext cost (len b') 1 u)
            (cong (2 *_) (step/ext cost (1 + len b') 1 u))
          )
      ⟩
        Int.+ (2 + len b') Int.+ (len b' Int.⊖ (2 * (1 + len b')))
      ≡⟨ IntP.distribʳ-⊖-+-pos (2 + len b') (len b') (2 * (1 + len b')) ⟩
        2 + len b' + len b' Int.⊖ 2 * (1 + len b')
      ≡⟨ P.cong (λ x → x Int.⊖ 2 * (1 + len b')) (+-assoc 2 (len b') (len b')) ⟩
        2 + (len b' + len b') Int.⊖ 2 * (1 + len b')
      ≡⟨ P.cong (λ x → 2 + (len b'  + len b') Int.⊖ x) (*-distribˡ-+ 2 1 (len b')) ⟩
        2 + (len b' + len b') Int.⊖ (2 * 1 + 2 * len b')
      ≡⟨ P.cong (λ x → 2 + x Int.⊖ (2 + 2 * len b')) (n+n≡2*n (len b')) ⟩
        2 + 2 * len b' Int.⊖ (2 + 2 * len b')
      ≡⟨ IntP.n⊖n≡0 (2 + 2 * len b') ⟩
        Int.0ℤ
      ∎
    )
    λ a f' →
      begin
        (Int.+ (op/cost op/deq (cons a f' , b))) Int.+ ((op/deq operateϕ (cons a f' , b)) Int.⊖ (ϕ (cons a f' , b)))
      ≡⟨⟩
        Int.+ (step cost 1 1) Int.+ (step cost 1 (len f' + 2 * len b) Int.⊖ (step cost 1 (1 + len f') + 2 * len b))
      ≡⟨
        cong₂ Int._+_
          (cong Int.+_ (step/ext cost 1 1 u))
          (cong₂ Int._⊖_
            (step/ext cost (len f' + 2 * len b) 1 u)
            (cong (_+ 2 * len b) (step/ext cost (1 + len f') 1 u))
          )
      ⟩
        Int.+ 1 Int.+ ((len f' + 2 * len b) Int.⊖ (1 + len f' + 2 * len b))
      ≡⟨ IntP.distribʳ-⊖-+-pos 1 (len f' + 2 * len b) (1 + len f' + 2 * len b) ⟩
        1 + (len f' + 2 * len b) Int.⊖ (1 + len f' + 2 * len b)
      ≡⟨ P.cong (λ x → x Int.⊖ (1 + len f' + 2 * len b)) (P.sym (+-assoc 1 (len f') (2 * len b))) ⟩
        1 + len f' + 2 * len b Int.⊖ (1 + len f' + 2 * len b)
      ≡⟨ IntP.n⊖n≡0 (1 + len f' + 2 * len b) ⟩
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
    2 * (1 + n)
    ∎
   where open ≡-Reasoning

  all2s/is/acost : ∀ l → ◯ (Amortized l (all2s (length l)))
  all2s/is/acost [] u = a/emp
  all2s/is/acost ((op/enq x) ∷ os) u = a/cons (op/enq x) 2 os (all2s (length os)) (enq/acost x u) (all2s/is/acost os u)
  all2s/is/acost (op/deq ∷ os) u = a/cons op/deq 2 os (all2s (length os)) (acost/weaken z≤n (deq/acost u)) (all2s/is/acost os u)

  fb/amortized : ∀ q l → ◯ (Int.+ (cost/seq l q) Int.≤  Int.+ (ϕ q + 2 * length l))
  fb/amortized q l u =
    begin
    Int.+ (cost/seq l q) ≤⟨ amortized≥cost q l (all2s (length l)) (all2s/is/acost l u) u ⟩
    Int.+ (ϕ q + lsum (all2s (length l))) ≡⟨ P.cong (λ x → Int.+ (ϕ q + x)) (sum2s (length l)) ⟩
    Int.+ (ϕ q + 2 * length l) ≤⟨ IntP.≤-refl ⟩
    Int.+ (ϕ q + 2 * length l)
    ∎
   where open IntP.≤-Reasoning

  -- Starting with an empty queue, a sequence of n operations costs at most 2 * n
  fb≤2*|l| : ∀ l → IsBounded Q (l operate/seq emp) (2 * length l)
  fb≤2*|l| l = bound/relax (λ u → IntP.drop‿+≤+ (fb/amortized emp l u)) (operate/seq≤cost/seq l emp)
