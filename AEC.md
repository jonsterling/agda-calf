# List of claims

* The entries in the list of claims are formatted as follows:
> _Section number_ | _claim_ | _file name_ | _function name(s)_
* Claims are listed in order of appearance.
* Evaluation of claims are explained in section [Evaluation](#Evaluation).

1. Section 2.4 | Theorem 2.1 | src/Examples/Id.agda | Easy.id≤id/cost
2. Section 2.4 | Theorem 2.2 | src/Examples/Id.agda | Hard.id≤id/cost/closed
3. Section 2.5 | Theorem 2.3 | src/Examples/Id.agda | easy≡hard
4. Section 2.7 | Theorem 2.4 | src/Calf/Noninterference.agda | oblivious
5. Section 2.7 | Theorem 2.5 | src/Calf/Noninterference.agda | constant
5. Section 2.7 | Theorem 2.6 | src/Calf/Noninterference.agda | optimization
6. Section 3.1 | Figure 4. (Return) | src/Calf/Types/Bounded.agda | bound/ret
6. Section 3.1 | Figure 4. (Step) | src/Calf/Types/Bounded.agda | bound/step
6. Section 3.1 | Figure 4. (Bind) | src/Calf/Types/Bounded.agda | bound/bind
6. Section 3.1 | Figure 4. (Relax) | src/Calf/Types/Bounded.agda | bound/relax
7. Section 4.1 | Theorem 4.1 | src/Examples/Gcd/Spec.agda | gcd≡spec/zero, gcd≡spec/suc
7. Section 4.1 | Theorem 4.2 | src/Examples/Gcd/Clocked.agda | gcd≤gcd/depth |
7. Section 4.1 | Theorem 4.3 | src/Examples/Gcd/Refine.agda | gcd/depth≤gcd/depth/closed
7. Section 4.1 | Corollary 4.4 | src/Examples/Gcd/Refine.agda | gcd≤gcd/depth/closed
8. Section 4.2 | Theorem 4.5 | src/Examples/Queue.agda | enq≤enq/cost, deq≤deq/cost/closed
8. Section 4.2 | Corollary 4.6 | src/Examples/Queue.agda | op≤op/cost
8. Section 4.2 | Lemma 4.7 | src/Examples/Queue.agda | op/seq≤op/seq/cost
8. Section 4.2 | Theorem 4.8 | src/Examples/Queue.agda | enq/acost, deq/acost
9. Section 4.2 | Theorem 4.9 | src/Examples/Queue.agda | op/seq/cost≤ϕ₀+2*|l|
9. Section 4.2 | Corollary 4.10 | src/Examples/Queue.agda | op/seq≤2*|l|

# Download, installation, and sanity-testing

<!-- VM? -->
## Download

### Haskell dependencies

* ghc: we have tested ghc versions 9.0.1 and 8.6.5
* cabal: we have tested cabal versions 3.4.0.0 and 2.4.0.0

If you are running a version of Linux or Windows, the easiest way to install ghc and cabal is haskell-platform:

https://www.haskell.org/platform/#linux

ghcup is recommended for Macos:
https://www.haskell.org/ghcup/

After this, you should have `cabal` installed. Check by running `cabal --version` on the command line. For us this returns the following:

> `cabal-install version 3.4.0.0`

In theory any cabal version that supports installing Agda version 2.6.2 will work.

### Agda
To use agda-calf you will need Agda version 2.6.2. First update the package listing with the following command:

> `cabal update`

Then install Agda:

> `cabal install Agda-2.6.2`

This may take a while. To test your installation, type `agda --version` on the command line, which should return `Agda version 2.6.2`.

### Installing the Agda standard library
agda-calf depends on the Agda standard library, so you will need to download the standard library and tell Agda where to look for it.

First download the tarball:

> `wget -O agda-stdlib.tar https://github.com/agda/agda-stdlib/archive/v1.7.tar.gz`

Extract the tarball, noting the directory that contains the extracted folder `agda-stdlib-1.7`:

> `tar -zxvf agda-stdlib.tar`

Now we need to register the library with Agda.
1. If it doesn't exist, create a directory called `.agda` in your home directory (on Macos and Linux you can do `mkdir ~/.agda`).
2. Now in `.agda`, create a file called `libraries`.
3. Inside `~/.agda/libraries`, write down the following line, where DIR is replaced with the directory in which you extracted the tarball:

> `DIR/agda-stdlib-1.7/standard-library.agda-lib`

### Installing agda-calf

First, clone the repository to a convenient directory:

> `git clone https://github.com/jonsterling/agda-calf.git`

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

To evaluate a single claim, navigate to the directory containing the file associated with that claim and run `agda filename` on the command line. Because the validity of each claim is equivalent to agda being able to typecheck the function with no errors, the expected output is that agda will finish running with no output.

For convenience, we have define a root file called `src/index.agda` that includes all the files contained in agda-calf, so running `agda index.agda` in the directory `src` will effectively evaluate all claims at once. Again the expected output is that agda finishes typechecking with no errors or textual outputs. Note that running `agda index.agda` should not take more than a minute.

# Artifact Description

For an overview of of the core implementation of agda-calf, please see the **Language Implementation** section in the top-level README.md. We also provide a listing of the case studies on cost verification in agda-calf in the **Examples** section. We recommend the interested reader to begin with the example `Examples.Id`.

For writing and verifying new programs in agda-calf, we recommend using vscode with the agda-mode extension.

You can download vscode here:

https://code.visualstudio.com/

The documentation for agda-mode in vscode can be found here:

https://github.com/banacorn/agda-mode-vscode


