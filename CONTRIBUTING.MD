# Contributing to Verbose Lean

The Lean 4 version is still in a preliminary form and things are changing a
lot, but contributions are already welcome (after some discussion to make sure
no effort is wasted).

## Files organization

The first thing to understand is the file hierarchy. The `Tactics` folder is
common to all languages. It implements all the actual work performed by
tactics, with the notable exception of the help tactic and the suggestion
widget. Then the `French` and `English` folders define the syntax of the
tactics and calls the code from the `Tactics` folder.

The difficulty with the help tactic and the widget is that they mix some
back-end work and some syntax work. Indeed they need to analyze the current
goal or the selected assumptions and then provide suggestions that are valid
syntax. They could produce strings instead of syntax objects, but this would
have a huge maintenance cost. Any modification of the tactic syntax would need
to be carefully propagated to the help tactic and the widget (there is
currently not unit test framework that would be able to properly test the
widget). So the files `Help.lean` and `Widget.lean` contains a lot of code that
is duplicated between the French and English versions.

There is no mechanism ensuring that every French syntax has an English
analogue, but having both in the same repository already makes it a lot less
painful than in the Lean 3 version which had separate repositories. The
synchronization between the example files is also done by hand, although it
would be a nice project to write a Lean program that automatically does the
translation.

Inside the `Tactics` folder, there are common files `Common.lean`,
`Initialize.lean` and `Notations.lean` that are not tied to any specific
tactic. Then the remaining files implements tactics, grouped by the first word
of their English syntax. Each of those tactic file has a corresponding file in
each language, with the same name.

In addition to those tactic files, each language folder has a file
`Statements.lean` defining the syntax for examples and exercises. There is also
a file `Tactics.lean` which imports all statements except for the help tactic.
This file is imported by `Help.lean` since the help tactics needs to know about
the syntax of all tactics. The widget file in turn needs the help tactics which
is used when users select exactly one assumption or the full goal. Then there
is a file `All.lean` importing everything for that language (tactics including
help, statements and the widget) and an `Example.lean` together with its
supporting tiny library `ExampleLib.lean` which defines convergent sequences
and continuous functions.

Note also that each tactic file in the language folders includes its own tests.
This is convenient at this early stage of development but we will probably
switch to using a test folder at some point. Also there is currently no
continuous integration setup, so it is important to run `lake build` before
pushing.
