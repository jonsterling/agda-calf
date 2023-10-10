# List of claims

| Section | Example | Statement | File | Name | Simplified |
|---------|---------|-----------|------|------|------------|
| Section 3.1 | Example 3.1 | $\textit{double}$ | [Examples.Decalf.Basic](./src/Examples/Decalf/Basic.agda) | `double` |
| Section 3.1 | Example 3.1 | $\textit{double}_\text{bound}$ | [Examples.Decalf.Basic](./src/Examples/Decalf/Basic.agda) | `double/bound` |
| Section 3.1 | Example 3.1 | $\textit{double} = \textit{double}_\text{bound}$ | [Examples.Decalf.Basic](./src/Examples/Decalf/Basic.agda) | `double/has-cost` |
| Section 3.1 | Example 3.1 | $\bigcirc(\textit{double} = \lambda n.\ \mathsf{ret}(2n))$ | [Examples.Decalf.Basic](./src/Examples/Decalf/Basic.agda) | `double/correct` |
| Section 3.1 | Example 3.2 | $\textit{insert}$ | [Examples.Sorting.Sequential.InsertionSort](./src/Examples/Sorting/Sequential/InsertionSort.agda) | `insert` |
| Section 3.1 | Example 3.2 | $\textit{insert}_\text{bound}$ | [Examples.Sorting.Sequential.InsertionSort](./src/Examples/Sorting/Sequential/InsertionSort.agda) | `insert/cost` | ✓ |
| Section 3.1 | Example 3.2 | $\textit{insert} \le \textit{insert}_\text{bound}$ | [Examples.Sorting.Sequential.InsertionSort](./src/Examples/Sorting/Sequential/InsertionSort.agda) | `insert/is-bounded` | ✓ |
| Section 3.1 | Example 3.4 | $\textit{isort}$ | [Examples.Sorting.Sequential.InsertionSort](./src/Examples/Sorting/Sequential/InsertionSort.agda) | `sort` |
| Section 3.1 | Example 3.4 | $\textit{isort}_\text{bound}$ | [Examples.Sorting.Sequential.InsertionSort](./src/Examples/Sorting/Sequential/InsertionSort.agda) | `sort/cost` | ✓ |
| Section 3.1 | Example 3.4 | $\textit{isort} \le \textit{isort}_\text{bound}$ | [Examples.Sorting.Sequential.InsertionSort](./src/Examples/Sorting/Sequential/InsertionSort.agda) | `sort/is-bounded` | ✓ |
| Section 3.1 | Example 3.4 | $\textit{msort}$ | [Examples.Sorting.Sequential.MergeSort](./src/Examples/Sorting/Sequential/MergeSort.agda) | `sort` |
| Section 3.1 | Example 3.4 | $\textit{msort}_\text{bound}$ | [Examples.Sorting.Sequential.MergeSort](./src/Examples/Sorting/Sequential/MergeSort.agda) | `sort/cost` | ✓ |
| Section 3.1 | Example 3.4 | $\textit{msort} \le \textit{msort}_\text{bound}$ | [Examples.Sorting.Sequential.MergeSort](./src/Examples/Sorting/Sequential/MergeSort.agda) | `sort/is-bounded` | ✓ |
| Section 3.1 | Theorem 3.5 | $\bigcirc(\textit{isort} = \textit{msort})$ | [Examples.Sorting.Sequential](./src/Examples/Sorting/Sequential.agda) | `isort≡msort` | ✓ |
| Section 3.2.1 | Example 3.6 | $\textit{qsort}$ | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `sort` |
| Section 3.2.1 | Example 3.6 | $\textit{qsort}$ bounded | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `sort/is-bounded` | ✓ |
| Section 3.2.1 | Example 3.7 | $\textit{lookup}$ | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `lookup` |
| Section 3.2.1 | Example 3.7 | $\textit{lookup}_\text{bound}$ | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `lookup/bound` |
| Section 3.2.1 | Example 3.8 | $e$ | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `e` |
| Section 3.2.1 | Example 3.8 | $e$ bounded | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `e/is-bounded` |
| Section 3.2.1 | Example 3.8 | $e;\mathsf{ret}(\star)$ bounded | [Examples.Decalf.Nondeterminism](./src/Examples/Decalf/Nondeterminism.agda) | `e/is-bounded'` |
| Section 3.2.2 | Example 3.9 | $\textit{sublist}$ | [Examples.Decalf.ProbabilisticChoice](./src/Examples/Decalf/ProbabilisticChoice.agda) | `sublist` |
| Section 3.2.2 | Example 3.9 | $\textit{bernoulli}$ | [Examples.Decalf.ProbabilisticChoice](./src/Examples/Decalf/ProbabilisticChoice.agda) | `bernoulli` |
| Section 3.2.2 | Example 3.9 | $\textit{binomial}$ | [Examples.Decalf.ProbabilisticChoice](./src/Examples/Decalf/ProbabilisticChoice.agda) | `binomial` |
| Section 3.2.2 | Example 3.9 | $\lambda l.\ (\textit{sublist}~l;\mathsf{ret}(\star))$ bounded | [Examples.Decalf.ProbabilisticChoice](./src/Examples/Decalf/ProbabilisticChoice.agda) | `sublist/is-bounded` |
| Section 3.2.2 | Example 3.9 | $\textit{binomial}$ bounded | [Examples.Decalf.ProbabilisticChoice](./src/Examples/Decalf/ProbabilisticChoice.agda) | `binomial/upper` |
| Section 3.2.2 | Example 3.9 | $\lambda l.\ (\textit{sublist}~l;\mathsf{ret}(\star))$ bounded (relaxed) | [Examples.Decalf.ProbabilisticChoice](./src/Examples/Decalf/ProbabilisticChoice.agda) | `sublist/is-bounded'` |
| Section 3.2.3 | Example 3.10 | $e$ | [Examples.Decalf.GlobalState](./src/Examples/Decalf/GlobalState.agda) | `e` |
| Section 3.2.3 | Example 3.10 | $e_\text{bound}$ | [Examples.Decalf.GlobalState](./src/Examples/Decalf/GlobalState.agda) | `e/bound` |
| Section 3.2.3 | Example 3.10 | $e = e_\text{bound}$ | [Examples.Decalf.GlobalState](./src/Examples/Decalf/GlobalState.agda) | `e/has-cost` |
| Section 3.3 | Example 3.11 | $\textit{twice}$ | [Examples.Decalf.HigherOrderFunction](./src/Examples/Decalf/HigherOrderFunction.agda) | `twice` |
| Section 3.3 | Example 3.11 | $\textit{twice}$ bounded (conditional) | [Examples.Decalf.HigherOrderFunction](./src/Examples/Decalf/HigherOrderFunction.agda) | `twice/is-bounded` |
| Section 3.3 | Example 3.12 | $\textit{map}$ | [Examples.Decalf.HigherOrderFunction](./src/Examples/Decalf/HigherOrderFunction.agda) | `map` |
| Section 3.3 | Example 3.12 | $\textit{map}$ bounded (fixed conditional) | [Examples.Decalf.HigherOrderFunction](./src/Examples/Decalf/HigherOrderFunction.agda) | `map/is-bounded` |
| Section 3.3 | Example 3.12 | $\textit{map}$ bounded (probabilistic conditional) | [Examples.Decalf.HigherOrderFunction](./src/Examples/Decalf/HigherOrderFunction.agda) | `map/is-bounded'` |

For simplicity, weaker cost bound proofs (eliding correctness proofs) for the sorting algorithms are given as indicated in the last column, following the original **calf** development of Niu et al. (2022).


# Download, installation, and sanity-testing

## Haskell dependencies

* `ghc`: we have tested `ghc` versions 8.10.2
* `cabal`: we have tested `cabal` version 3.4.0.0

If you are running a version of Linux or Windows, the easiest way to install `ghc` and `cabal` is [haskell-platform](https://www.haskell.org/platform/#linux).
For MacOS, [GHCup](https://www.haskell.org/ghcup/) is recommended.

After this, you should have `cabal` installed. Check by running `cabal --version` on the command line. For us this returns the following:

> `cabal-install version 3.4.0.0`

In theory, any `cabal` version that supports installing Agda version 2.6.3 will work.

## Agda

To use `agda-calf`, you will need Agda version 2.6.3. First update the package listing with the following command:

> `cabal update`

Then install Agda:

> `cabal install Agda-2.6.3`

This may take a while. To test your installation, type `agda --version` on the command line, which should return `Agda version 2.6.3`.

## Installing the Agda standard library

`agda-calf` depends on the Agda standard library, so you will need to download the standard library and tell Agda where to look for it.

First download the library:

> `wget -O agda-stdlib.tar https://github.com/agda/agda-stdlib/archive/refs/heads/master.tar.gz`

Extract the tarball, noting the directory that contains the extracted folder `agda-stdlib-master`:

> `tar -zxvf agda-stdlib.tar`

Now we need to register the library with Agda.
1. If it doesn't exist, create a directory called `.agda` in your home directory (on MacOS and Linux you can do `mkdir ~/.agda`).
2. Now in `.agda`, create a file called `libraries`.
3. Inside `~/.agda/libraries`, write down the following line, where DIR is replaced with the directory in which you extracted the tarball:

> `DIR/agda-stdlib-master/standard-library.agda-lib`

## Installing `agda-calf`

Clone the repository to a convenient directory:

> `git clone https://github.com/jonsterling/`agda-calf`.git`

The directory structure of `agda-calf` should be as follows (omitting some files and directories):

```
agda-calf
└───src
│   └───Calf
│   │   index.agda
│   AEC.md
│   README.md
```

Note that the files relevant to the claims are all located in the `src` directory.

# Evaluation

To evaluate a single claim, navigate to the directory containing the file associated with that claim and run `agda filename` on the command line.
Because the validity of each claim is equivalent to Agda being able to typecheck the function with no errors, the expected output is that Agda will finish running with no output.

For convenience, we have define a root file [src/index.agda](./src/index.agda) that includes all the files contained in `agda-calf`, so running `agda index.agda` in the directory `src` will effectively evaluate all claims at once.
Again, the expected output is that Agda finishes typechecking with no errors or textual outputs.
Note that running `agda index.agda` should not take more than a few minutes.

# Artifact description

For an overview of the core implementation of `agda-calf`, please see the **Language Implementation** section in the top-level [README.md](./README.md).
We also provide a listing of the case studies on cost verification in `agda-calf` in the **Examples** section; some additional examples are updated from **calf** to **decalf**.
We recommend the interested reader to begin with the example `Examples.Id`.

One can also view `agda-calf` online here: https://jonsterling.github.io/agda-calf/

For writing and verifying new programs in `agda-calf`, we recommend using [VS Code](https://code.visualstudio.com/) with the [agda-mode](https://github.com/banacorn/agda-mode-vscode) extension.
