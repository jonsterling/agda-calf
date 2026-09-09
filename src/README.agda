module README where

{-
  This file is a curated guide to the PFAT mechanization, ordered by the
  presentation in the paper.

  The formalization is checked against Agda v2.8.0 with standard library v2.3
  and cubical library v0.9.
  The mechanization covers the value- and computation-level
  modalities, fracture/gluing, potential functions as types, credits/debits,
  the batched-queue example, and the Giralf as embedded in Calf.
-}

-- Section 2. The Physicist's View

-- Section 2.1. Abstraction Functions as Types

{-
    Definition 2.1. Abstract value types and the open modality.
-}
import Calf.Value.Open using
  ( ◯
  ; η◦
  ; 𝒱◦
  )

{-
    Definition 2.2. Concrete value types and the closed modality.
-}
import Calf.Value.Closed using
  ( ●
  ; η•
  ; ∗
  ; push
  ; 𝒱•
  ; ◯-isConnected
  )

{-
    Theorem 2.3. Value-level fracture and gluing.
    Corollary 2.4. Maps out of glued value types are squares.
-}
import Calf.Value.Glue using
  ( Glue
  ; Fracture
  ; fromFracture
  ; toFracture
  ; square
  ; fracture-and-gluing
  ; fracture-and-gluing-square
  )

{-
    Definition 2.5. Building an ordinary abstraction function into a value type.
    Corollary 2.6. Identity abstraction.
    Lemma 2.7. It suffices to define coherent concrete and abstract maps.
-}
import Calf.Value.Abstraction using
  ( Abstraction
  ; Abstraction-id
  ; square
  )

-- Section 2.2. Potential Functions as Types

{-
    Definition 2.9. Abstract computation types and the open computation
    modality.
    Lemma 2.13. U commutes with the open modalities.
    Lemma 2.14. The modality is lex, preserving pullbacks.
-}
import Calf.Computation.Open using
  ( ◯ᶜ
  ; η◦ᶜ
  ; 𝒞◦
  ; U◦
  ; Pullback-◯ᶜ
  )

{-
    Definition 2.10. Concrete computation types and the closed computation
    modality.
    Lemma 2.13. U commutes with the open and closed modalities.
    Lemma 2.14. The modality is lex, preserving pullbacks.
-}
import Calf.Computation.Closed using
  ( ●ᶜ
  ; η•ᶜ
  ; 𝒞•
  ; U•
  ; Pullback-●ᶜ
  )

{-
    Definitions 2.11 and 2.12. Cost algebras, strict homomorphisms, cost effects, and
    conservativity of the underlying value type functor.
-}
import Calf.Computation using
  ( 𝒞
  ; charge
  ; _⊸_
  ; conservativity
  )

{-
    Supporting computation type formers used by Section 2 examples and later
    amortized data-structure constructions.
-}
import Calf.Computation.Free using
  ( F
  )
import Calf.Computation.Copower using
  ( Σᶜ
  ; _⋊_
  )
import Calf.Computation.Product using
  ( _×ᶜ_
  )
import Calf.Computation.Power using
  ( _⇀_
  )
import Calf.Computation.Tensor using
  ( _⊗_
  )

{-
    Theorem 2.15. Computation-level fracture and gluing.
    Corollary 2.16. Homomorphisms out of glued computation types are squares.
-}
import Calf.Computation.Glue using
  ( Glueᶜ
  ; Fractureᶜ
  ; fromFractureᶜ
  ; toFractureᶜ
  ; squareᶜ
  ; fracture-and-gluingᶜ
  ; fracture-and-gluing-squareᶜ
  )

{-
    Definition 2.17. Building a homomorphism, hence a potential function, into
    a computation type.
    Corollary 2.18. Identity abstraction.
    Lemma 2.19. It suffices to define coherent concrete and abstract maps.
    Corollary 2.23. One-sided maps into or out of glued computation types.
-}
import Calf.Computation.Abstraction using
  ( Abstractionᶜ
  ; Abstractionᶜ-id
  ; squareᶜ
  ; triangle-abs
  ; triangle-⊤
  )

-- Section 2.3. Potential and Abstraction, Independently

{-
    Definition 2.21. Potential functions as computation types.
    Lemma 2.22. Homomorphisms between potential-carrying types follow from the
    usual potential-conservation equation.
-}
import Calf.Computation.Potential using
  ( Potential
  ; square
  )

{-
  Section 2 and Section 3. Modularity and the batched-queue case study.
-}
{-
    Example 2.20. The cost-aware ephemeral batched queue.
    Example 3.3. Ephemeral queue cost interface.
-}
import Examples.Queue using
  ( PreQueue
  ; Queue
  ; list-prequeue
  ; α
  ; batched-queue
  )

{-
  Section 3.2. Sealing and lax commutative squares.
-}
{-
    Definitions of the sealing monad and lax homomorphisms.
    Lemma 3.5. The sealing monad is abstractly trivial.
-}
import Calf.Computation.Seal using
  ( Sealᶜ
  ; _⊸ᵈ_
  ; idᵈ
  ; _⨾ᵈ_
  ; Sealᶜ-open
  )

-- Section 4. The Banker's View

-- Section 4.1. Credits and Debits

{-
    Definition 4.1. The credit operator.
    Lemma 4.4. Credits are invisible to the modalities.
    Lemma 4.5. Credits admit weakening.
    Lemma 4.6. Credits compose monoidally.
    Definition 4.7. Saving and spending credits.
    Lemma 4.8. Spending after saving is the cost effect.
-}
import Calf.Computation.Credit using
  ( ▷[_]_
  ; ▷-●ᶜ
  ; ▷-◯ᶜ
  ; waste
  ; ▷-0
  ; ▷-+
  ; save
  ; spend
  ; save⨾spend≡chargeᶜ
  )
{-
    Lemma 4.10. Potential can be recharacterized as credits.
-}
import Calf.Computation.Potential using
  ( Potential-credit
  )

{-
    Definition 4.11. The debit operator.
    Lemma 4.12. Credit and debit are adjoint.
-}
import Calf.Computation.Debit using
  ( ◁[_]_
  ; ▷⊣◁
  ; ▷⊣◁-counit
  )

-- Section 4.2. Credit-Carrying Lists.

{-
    Definition 4.13. Linear-credit lists.
    Corollary 4.14. Linear-credit lists are abstractly lists.
    Definition 4.18. Linear-and-triangular-credit lists.
    Corollary 4.19. Linear-and-triangular-credit lists are abstractly lists.
-}
import Calf.Computation.CList1 using
  ( CList₁
  ; nil₁
  ; cons₁
  ; foldr₁
  ; CList₁-open
  )
import Calf.Computation.CList2 using
  ( CList₂
  ; nil₂
  ; cons₂
  ; foldr₂
  ; CList₂-open
  )

-- Section 5. Giralf: A Graded, Inferential, Resource-Aware Logical Framework

-- Section 5.1. A Graded Syntax
-- Section 5.2. A Resource-Aware Semantics

{-
    Examples 5.2 and 5.3. Insertion and insertion sort.
    Example 5.4. Resource-aware semantics of credit storage and spending.
-}
import Calf.Giralf using
  ( Context
  ; _⋎₀
  ; _⋎₂_
  ; _⊢_
  ; idᴳ
  ; letᴳ
  ; cmpᴳ
  ; cmpᴳ→cmp
  ; cmp→cmpᴳ
  ; substᵐᴳ
  ; substᴳ
  ; subst2ᴳ
  ; subst3ᴳ
  ; storeᴳ
  ; releaseᴳ
  ; spendᴳ
  ; getᴳ
  ; payᴳ
  ; nil₁ᴳ
  ; cons₁ᴳ
  ; foldr₁ᴳ
  ; nil₂ᴳ
  ; cons₂ᴳ
  ; foldr₂ᴳ
  ; pairᴳ
  ; proj₁ᴳ
  ; proj₂ᴳ
  ; powlamᴳ
  ; powappᴳ
  )
import Examples.Giralf.Id using
  ( id₁
  ; id₂
  )
import Examples.Giralf.Reverse using
  ( snoc
  ; qreverse
  )
import Examples.Giralf.InsertionSort using
  ( insert
  ; isort
  )

{-
    Theorem 5.7. AARA types can be rendered as Potential types.
-}
import Calf.Giralf.AARA using
  ( aara-potential
  )

-- Section 5.3. An Inference Algorithm

{-
    These examples are generated by the inference algorithm.
-}
import Examples.Giralf.Inference using
  ( snoc
  ; insert
  ; reverse
  ; isort
  )
