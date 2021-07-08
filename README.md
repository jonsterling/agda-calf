# **calf**: A Cost-Aware Logical Framework

The **calf** language is a **c**ost-**a**ware **l**ogical **f**ramework for studying quantitative aspects of functional programs.

This repository contains the Agda implementation of **calf**, as well as some case studies of varying complexity.

## Installation

This implementation of **calf** has been tested using:
- Agda v2.6.2
- `agda-stdlib` v1.7

Installation instructions may be found in [`INSTALL.md`](./INSTALL.md).

## Language Implementation

### Cost Monoid Parameterization

**calf** is parameterized by a *cost monoid* `(ℂ, +, zero, ≤)`.
The formal definition, `CostMonoid`, is given in [`Calf.CostMonoid`](./src/Calf/CostMonoid.agda).
The definition of a *parallel cost monoid* `(ℂ, ⊕, 𝟘, ⊗, 𝟙, ≤)` is given, as well, as `ParCostMonoid`.

Some common cost monoids and parallel cost monoids are given in [`Calf.CostMonoids`](./src/Calf/CostMonoids.agda); for example, `ℕ-CostMonoid` simply tracks sequential cost.
Note that every `ParCostMonoid` induces a `CostMonoid` via the additive structure, `(ℂ, ⊕, 𝟘, ≤)`.

### Core Language

The language itself is implemented via the following files, which are given in a dependency-respecting order.

The following modules are not parameterized:
- [`Calf.Prelude`](./src/Calf/Prelude.agda) contains commonly-used definitions.
- [`Calf.Metalanguage`](./src/Calf/Metalanguage.agda) defines the basic Call-By-Push-Value (CBPV) language, using Agda `postulate`s and rewrite rules.
- [`Calf.PhaseDistinction`](./src/Calf/PhaseDistinction.agda) defines the phase distinction for extension, including the extensional open `ext`, the open modality `◯`, and the closed modality `●`.
- [`Calf.Noninterference`](./src/Calf/Noninterference.agda) gives theorems related to the phase distinction/noninterference.

The following modules are parameterized by a `CostMonoid`:
- [`Calf.Step`](./src/Calf/Step.agda) defines the `step` effect and gives the associated laws via rewrite rules.

The following modules are parameterized by a `ParCostMonoid`:
- [`Calf.ParMetalanguage`](./src/Calf/ParMetalanguage.agda) the (negative) parallel product `_&_`, whose cost is the `ParCostMonoid` product (i.e., `_⊗_`) of its components, as well as associated laws and lemmas.

### Types

In [`src/Calf/Types`](./src/Calf/Types), we provide commonly-used types.

The following modules are not parameterized:
- [`Calf.Types.Nat`](./src/Calf/Types/Nat.agda), [`Calf.Types.Unit`](./src/Calf/Types/Unit.agda), [`Calf.Types.Bool`](./src/Calf/Types/Bool.agda), [`Calf.Types.Sum`](./src/Calf/Types/Sum.agda), and [`Calf.Types.List`](./src/Calf/Types/List.agda) internalize the associated Agda types via `meta`.
  Notably, this means that their use does *not* incur cost.
- [`Calf.Types.Eq`](./src/Calf/Types/Eq.agda) defines the equality type.

The following modules are parameterized by a `CostMonoid`:
- [`Calf.Types.Bounded`](./src/Calf/Types/Bounded.agda) defines a record `IsBounded A e c` that contains a proof that the cost of `e` (of type `A`) is bounded by `c : ℂ`.
  Additionally, it provides lemmas for proving the boundedness of common forms of computations.
- [`Calf.Types.BoundedFunction`](./src/Calf/Types/BoundedFunction.agda) defines cost-bounded functions using `IsBounded`.
- [`Calf.Types.BigO`](./src/Calf/Types/BoundedFunction.agda) gives a definition of "big-O" asymptic bounds as a relaxation of `IsBounded`.

## Examples
- Id
- Gcd
- Queue
- TreeSum
- Exp2
- Sorting
- CostEffect
