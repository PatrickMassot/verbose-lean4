# Verbose Lean 4

This project provides tactics and commands for
[Lean](https://leanprover-community.github.io/) in a very controlled
natural language. The original version of those tactics were written in
French for teaching purposes at 
[Université Paris-Saclay](https://www.universite-paris-saclay.fr/) in
Orsay using Lean 3. The goal is not to make Lean code easier to write, the goal is to
make Lean code easier to transfer to a traditional paper proof.

The best way to have a quick look is to read the examples file
in [English](https://github.com/PatrickMassot/verbose-lean4/blob/master/Verbose/English/Examples.lean) or 
[French](https://github.com/PatrickMassot/verbose-lean4/blob/master/Verbose/French/Examples.lean),
although GitHub obviously misses proper syntax highlighting here. 

There is also a point-and-click interface for courses with a low time budget. One can see it in the following animated gif.

![Point-and-click interface](verbose_widget_test_en.gif)

You can read [a paper](itp2024_paper.pdf) written about this library for 
[ITP2024](https://www.viam.science.tsu.ge/itp2024/).

This Lean 4 version is not yet well tested since it has not been used a lot for teaching yet. It is currently used in Strasbourg.
If you use those tactics for teaching, I'd be very interested to hear about it, and would gladly add your name and the name of your university in this file.

If you want to try it or start writing your exercises using it then you
should read [getting-started.md](getting-started.md). Then you can tweak the
behavior of tactics using the [basic configuration guide](basic-configuration.md).
For information about translating those tactics to your language, see the
[translation guide](translations.md).

If you simply want to play a bit with the example shown in the picture above
then you can 
[![Open the project in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/new/#https://github.com/patrickmassot/verbose-lean4) 
and use the file explorer to open the file `Verbose/English/Examples.lean`.
