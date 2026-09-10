# **Equations** - a function definition plugin.

[![Build Status](https://github.com/rocq-prover/equations/actions/workflows/build.yml/badge.svg?branch=main&event=push)](https://github.com/rocq-prover/equations/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.3012649.svg)](https://zenodo.org/record/3012649#.XcEydZNKjOQ)
[![Zulip Chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/237659-Equations-devs.20.26.20users)

Copyright 2009-2025 Matthieu Sozeau `matthieu.sozeau@inria.fr`
Copyright 2015-2018 Cyprien Mangin `cyprien.mangin@m4x.org`

Distributed under the terms of the GNU Lesser General Public License
Version 2.1 or later
(see
[LICENSE](http://github.com/rocq-prover/equations/raw/master/LICENSE)
for details).

Equations provides a notation for writing programs by dependent
pattern-matching and (well-founded) recursion
in [Coq](http://coq.inria.fr). It compiles everything down to
eliminators for inductive types, equality and accessibility,
providing a definitional extension to the Coq kernel.
The plugin can be used with Coq's standard logic in `Prop`
for a proof-irrelevant, erasable interpretation of pattern-matching,
or with a polymorphic logic in `Type` or re-using the prelude
of the [HoTT/Coq](http://github.com/HoTT/HoTT) library for a
proof-relevant interpretation. In all cases, the resulting
definitions are axiom-free.

***Table of Contents***

- [**Equations** - a function definition plugin.](#equations---a-function-definition-plugin)
  - [Learning Equations](#learning-equations)
  - [Documentation](#documentation)
  - [Papers and presentations](#papers-and-presentations)
  - [Installation](#installation)
    - [Install with OPAM](#install-with-opam)
    - [Install from source](#install-from-source)
  - [HoTT Variant](#hott-variant)

## Learning Equations

- You can discover and learn Equations through [interactive tutorials](https://coq.inria.fr/platform-docs/)
  directly in your browser, or locally with Equations installed.

## Documentation

- The [reference manual](http://github.com/rocq-prover/equations/raw/main/doc/equations.pdf)
  provides a summary of the commands and options, and a brief introduction.
  This introduction can also be followed interactively with Equations installed,
  [equations_intro.v](http://github.com/rocq-prover/equations/raw/main/doc/equations_intro.v)
  or [interactively in your browser](http://rocq-prover.github.io/equations/assets/jsexamples/equations_intro.html).

- A gallery of [examples](http://rocq-prover.github.io/equations/examples) provides more consequent
  developments using Equations.

## Papers and presentations

- [Equations Reloaded: High-Level Dependently-Typed Functional Programming and Proving in Coq](https://sozeau.gitlabpages.inria.fr/www/research/publications/Equations_Reloaded-ICFP19.pdf). Matthieu Sozeau and Cyprien Mangin.
  In: Proc. ACM Program. Lang. 3, ICFP, Article 86 (August 2019), 29 pages. [DOI](https://doi.org/10.1145/3341690),
  [slides](https://sozeau.gitlabpages.inria.fr/www/research/publications/Equations_Reloaded-ICFP19-190819.pdf).

  This presents version 1.2 and above of the package.
  See [Equations Reloaded](equations-reloaded) for associated material, including a VM to run the examples.

- [Equations for HoTT](https://sozeau.gitlabpages.inria.fr/www/research/publications/Equations_for_HoTT-HoTT19-130819.pdf).
  Matthieu Sozeau, Talk given at the [Homotopy Type Theory 2019](https://hott.github.io/HoTT-2019//programme/#sozeau)
  Conference in Pittsburgh, PA, August 2019.

  This explains the no-confusion principle and strong equivalences
  used by Equations and Jesper Cockx's version of dependent pattern-matching in Agda
  in terms of HoTT.

- [Equations for Hereditary Substitution in Leivant's Predicative System F: A Case Study](https://sozeau.gitlabpages.inria.fr/www/research/publications/Equations_for_Hereditary_Substitution_in_Leivants_Predicative_System_F:_a_case_study.pdf).
  Cyprien Mangin and Matthieu Sozeau.
  In: Proceedings Tenth International Workshop on Logical Frameworks and Meta Languages: Theory and Practice.
  Volume 185 of EPTCS. May 2015 - LFMTP'15.

  This is a case study on a proof of normalization for an hereditary substitution procedure on a variant of System F.

- [Equations: A Dependent Pattern-Matching Compiler](https://link.springer.com/chapter/10.1007/978-3-642-14052-5_29) Matthieu
  Sozeau (2010)
  In: Kaufmann M., Paulson L.C. (eds) Interactive Theorem
  Proving. ITP 2010. Lecture Notes in Computer Science,
  vol 6172. Springer, Berlin, Heidelberg.

  This presents an earlier version of the package.

## Installation

The latest version works with Coq 8.13 (branch
[8.13](https://github.com/rocq-prover/equations/tree/8.13)),
Coq 8.14 (branch
[8.14](https://github.com/rocq-prover/equations/tree/8.14)),
Coq 8.15 (branch
[8.15](https://github.com/rocq-prover/equations/tree/8.15)),
and the current Coq master branch (branch
[master](https://github.com/rocq-prover/equations/tree/master)).

See [releases](https://github.com/rocq-prover/equations/releases) for
sources and official releases.

### Install with OPAM

This package is available on [OPAM](http://opam.ocaml.org/).
Activate the [Coq repository](https://coq.inria.fr/opam-using.html)
if you didn't do it yet:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-equations

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

To get the development version of Equations, activate the repository:

    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

### Install from source

Alternatively, to compile Equations, simply run:

    ./configure.sh
    make

in the toplevel directory, with `coqc` and `ocamlc` in your path.

Optionally, one can build the test-suite or examples:

    make examples test-suite

Then add the paths to your `.coqrc`:

    Add ML Path "/Users/mat/research/coq/equations/src".
    Add Rec LoadPath "/Users/mat/research/coq/equations/theories" as Equations.

Or install it:

    make install

As usual, you will need to run this command with the appropriate privileges
if the version of Coq you are using is installed system-wide, rather than
in your own directory. E.g. on Ubuntu, you would prefix the command with
`sudo` and then enter your user account password when prompted.

## HoTT Variant

The HoTT variant of Equations works with the coq-hott library for Coq 8.13 and up. When using `opam`, simply install first the `coq-hott` library and `coq-equations` will install its HoTT variant. From source, first
install `coq-hott` and then use:

    ./configure.sh --enable-hott

This will compile the `HoTT` library variant in addition to the standard one.
Then, after `make install`, one can import the plugin in Coq, using:

    From Equations Require Import HoTT.All.