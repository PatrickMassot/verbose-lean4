# Basic configuration of Verbose Lean

Verbose Lean offers many levels of customization.
If you know about Lean meta-programming, you can see this library as a
meta-library that allows you to build your teaching library.
But in this file we focus on customization that can be achieved without any
programming.

## Boolean configuration options

At any point you can print the current configuration with
`#print_verbose_config`.

The first configuration option is the language code option.
The default language code is `en` which denotes my version of English.
The library also ships with French support that can be activated using
```lean
setLang fr
```

Then there are a number of boolean configuration options that can be set using
the following commands:

* `enableUnfoldingSuggestions`/`disableUnfoldingSuggestions` allows to switch on
  and off suggestions of definition unfolding. The default is on.
* `enableHelpTactic`/`disableHelpTactic` allows to activate or deactivate the
  help tactic. The default is activated.
* `enableWidget`/`disableWidget` allows to activate or deactivate the
  suggestion widget. The default is activated.
* `debugWidget` turns on debug messages for the suggestion widget. There is no
  command turning it off, you simply need to delete this command when you are
  done debugging.
* `allowProvingNegationsByContradiction` turns off the error message that
  appears when users try to prove a negation by contradiction.

## Declarations lists

Then many configuration options take lists of declarations. Since those lists
could be long and difficult to read, you can declare (nested) lists of declarations.

For instance, the `configureUnfoldableDefs` command wants a list of declaration
names. Those are the declarations whose unfolding will be suggested by the help
tactic or the suggestion widget. Say you want to suggest unfolding of
`continous_at`, `continuous`, `sequentially_continuous`, `seq_tends_to`,
`seq_is_bounded`, `monotone` and `divides` (those are partially made names). You could
define lists of unfoldable definitions and configure the library by:
```
UnfoldableDefsList FunctionStuff := continuous continuous_at sequentially_continuous

UnfoldableDefsList SequenceStuff := seq_tends_to seq_is_bounded

UnfoldableDefsList AnalysisStuff := FunctionStuff SequenceStuff monotone

configureUnfoldableDefs AnalysisStuff divides
```

Notice how the definition of `AnalysisStuff` and the configuration line mix
previously defined lists with individual declaration names.

If you define many lists in many different files then you could enjoy using the
`#unfoldable_defs_lists` command to list all your lists and their content.

This mechanism is used by the following configuration options. For each one we
indicate the configuration command, the command that creates a list, and the
function that prints existing lists.
What those declarations lists are good for will be described in the next
sections.

* Unfoldable definitions: `configureUnfoldableDefs`/`UnfoldableDefsList`/`#unfoldable_defs_lists`
* Help provider functions: `configureHelpProviders`/`HelpProviderList`/`#help_provider_lists`
* Anonymous goal splitting lemmas:
  `configureAnonymousGoalSplittingLemmas`/`AnonymousGoalSplittingLemmasList`/`#anonymous_goal_splitting_lemmas_lists`
* Anonymous fact splitting lemmas:
  `configureAnonymousFactSplittingLemmas`/`AnonymousFactSplittingLemmasList`/`#anonymous_fact_splitting_lemmas_lists`

* Suggestions provider functions: `configureSuggestionProviders`/`SuggestionProviderList`/`#suggestions_provider_lists`
* Data provider functions: `configureDataProviders`/`DataProviderList`/`#data_provider_lists`


## Anonymous lemmas

Anonymous lemmas are lemmas that the library will use without needing to refer
to their names. They are meant to be lemmas that have no name on paper and are
used implicitly. But of course they have names in Lean and those are the names
that go into `configureAnonymousGoalSplittingLemmas` and `configureAnonymousFactSplittingLemmas`.

The goal splitting lemmas are lemmas that turn a single goal into several goals.
They are used by the tactic `Let’s first prove that …`.
The tautological example is the `And.intro` lemma that they that in order to
prove `P ∧ Q`, it is sufficient to prove `P` and to prove `Q`.
The library also provides a variant swapping `P` and `Q` so that you can start
with the proof of `Q`. There are analogue lemmas allowing to prove an
equivalence by proving two implications. Those four lemmas are gathered in the
`LogicIntros` lemma list.

Slightly less obvious candidates to by anonymous goal splitting lemmas are the
lemma proving a set equality by double inclusion or the lemmas proving
inequalities about absolute values from pairs of inequalities.

The fact splitting lemmas are lemmas that can be used to get several facts out
of one. The tautological example would be splitting a conjunction, but the
library actually has dedicated support for that. An actual typical example
would be a lemma splitting `x ≥ max a b` into `x ≥ a` and `x ≥ b`.

## Help and suggestion providers

Help providers are function used by the `help` tactic. Technically there are
two kinds of them: those providing help about the current goal and those
providing help about a local assumption. But they are handled by the same
configuration option.

One cannot write such a help function without programming skills, so discussing
how they work is outside of the scope of this document. However it is easy to
notice a help message that you don’t want, search where it comes from and remove
the corresponding function from the configuration. The default configuration
is obtained by `configureHelpProviders DefaultHypHelp DefaultGoalHelp`
so you can search for those two lists. It also worth mentioning that they don’t
include help functions suggesting contraposition or proofs by contradiction,
especially since the latter triggers on *every* goal. Those help function
are called `helpContraposeGoal` and `helpByContradictionGoal` so you can enable
them using
```
configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal helpByContradictionGoal
```

Similarly, the suggestion widget uses suggestion provider in addition to the
above help providers. Those cannot be written without programming skills. But
one of them is configurable without such skills: the one that creates data
for existential quantifier instantiation and universal quantifier
specialization out of the current info-view selection. This is done using
so-called data providers. Those data providers are purely syntactic
transformations, without any type constraints, and then they are assigned to
types. The default configuration is currently:
```
dataProvider mkSelf a := a

dataProvider mkHalf a := a/2

dataProvider mkAddOne a := a + 1

dataProvider mkMin a b := min a b

dataProvider mkMax a b := max a b

dataProvider mkAdd a b := a + b

/-- Default data providers for numbers type, including adding one, taking the min, max and sum
of two numbers. -/
DataProviderList NumbersDefault := mkAddOne mkMin mkMax mkAdd

configureDataProviders {
  ℝ : [mkSelf, mkHalf, NumbersDefault],
  ℕ : [mkSelf, NumbersDefault] }
```
This is hopefully easy to understand and modify.
