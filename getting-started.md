# Getting started

This document assumes you already installed Lean. 
See https://lean-lang.org/lean4/doc/quickstart.html 
if you need help doing that.

In order to use Verbose Lean in your teaching, you need to create a Lean
project. You can do that from the VSCode Lean menu or type in a terminal
`lake new teaching lib` to create a `teaching` folder with a Lean project layout
(do not use any fancy character in the name of your folder).

You need to make sure your project uses the same lean version as Verbose Lean.
For this you can copy the content of the Verbose Lean
[lean-toolchain file](https://github.com/PatrickMassot/verbose-lean4/blob/master/lean-toolchain)
to the lean-toolchain file of your project (this file is automatically created
by `lake init` in the root folder of your project).

Then you need to require the library in your lake file. 
This means adding at the end of `lakefile.toml` in your project:
```
[[require]]
name = "verbose"
git = "https://github.com/PatrickMassot/verbose-lean4.git"
rev = "master"
```

Important note in case you had an existing project: 
Verbose Lean will require Mathlib for you, so your `lakefile.lean` should *not*
contain a `require mathlib` line, otherwise you could be creating version
conflicts.

After adding the above `require`, you need to run `lake update verbose`
from your project folder. 
This will update your `lake-manifest.json` file and download Verbose Lean with
all its dependencies. 
This is large download since it includes a compiled Mathlib. 

Assuming you use the `teaching` name, your `teaching` folder now contains a
`Teaching` folder where all your Lean files go. It also contains a
`Teaching.lean` file which should import all files from the `Teaching` folder that
you want `lake build` to build (this typically means all files except for throw
away test files). Beware that Lean file whose name start with a number only
create pain.

You now need to create at least one teacher file that imports Verbose, configures it and
contains definitions you want to work with. Then you can create student files
with explanations and exercises.

For instance you can create in the `Teaching` folder a file `Math101.lean`
containing:
```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Verbose.English.All

open Verbose English

-- Let’s define mathematical notions here

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- and some nice notation

notation3:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation3:50 u:80 " converges to " l => sequence_tendsto u l

-- Now configure Verbose Lean 
-- (those configuration commands are explained elsewhere)

configureUnfoldableDefs continuous_function_at sequence_tendsto 

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros 

useDefaultDataProviders

useDefaultSuggestionProviders
```

and a `HomeWork1.lean` file containing:

```lean
import Teaching.Math101

Example "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  Since f is continuous at x₀ and ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Since u converges to x₀ and δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we get h : |u n - x₀| ≤ δ
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε and |u n - x₀| ≤ δ we conclude that |f (u n) - f x₀| ≤ ε 
QED
```

Assuming the installation process succeeded, Lean should be happy to process
those files. You can then learn more about this library.
