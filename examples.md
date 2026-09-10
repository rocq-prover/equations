---
layout: page
permalink: /examples/
title: Gallery of programs and proofs
---

Learning Equations
==================

- You can discover and learn Equations through [interactive tutorials](https://rocq-prover.org/docs/equations-docs)
  directly in your browser, or locally with Equations installed.

You can also check out the following introduction material to Equations
- [Intro](equations_intro.html): introduction to Equations, demonstrating
  its features
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/doc/equations_intro.v),
  [JSCoq](../assets/jsexamples/equations_intro.html)).

- [Basics](examples/Examples.Basics.html): Basic examples of Equations usage
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/Basics.v)).

Dependent Pattern-Matching
==========================

- [Vectors](examples/Examples.working_with_vectors.html): an example use to program 
  with vectors *and* reason on the defined functions
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/working_with_vectors.v)).

- [Polynomials](examples/Examples.polynomials.html): a reflexive tactic for
  solving boolean tautologies (initial version by Rafaël Bocquet)
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/polynomials.v)).

- [HoTT_light](examples/Examples.HoTT_light.html): basics of the HoTT library
  implemented using a logic in `Type`
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/HoTT_light.v)).

- [MoreDep](examples/Examples.MoreDep.html): part of chapter 8 of Adam
  Chlipala's [CPDT](http://adam.chlipala.net/cpdt/html/toc.html)
  (original version by Cyprien Mangin)
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/MoreDep.v)).

- [Definitional interpreter](examples/Examples.definterp.html): definitional interpreter
  for an impure language using well-scoped, well-typed syntax
  (porting Poulsen et al's POPL18
  [paper](http://casperbp.net/papers/intrinsicallytyped.html) on
  Intrisically-Typed Definitional Interpreters for Imperative Languages)
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/definterp.v)).

- [POPLMark 1a](examples/Examples.POPLMark1a.html): a solution to
  POPLMark 1a using well-scoped, well-typed syntax by Rafaël Bocquet,
  adapted to avoid UIP using equalities in constructors by Matthieu Sozeau.
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/POPLMark1a.v)).

- [Views](examples/Examples.views.html): using dependent pattern-matching with
  views, to handle default cases in pattern-matching
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/views.v)).

Recursion
=========

- [STLC](examples/Examples.STLC.html): strong normalization of simply-typed
  lambda-calculus with products using hereditary substitutions
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/STLC.v)).

- [String Matching](examples/Examples.string_matching.html): beginning of example
  by Nicky Vazou on string matching, uses well-founded recursion
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/string_matching.v)).

- [Rose Trees](examples/Examples.RoseTree.html): nested well-founded recursion
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/RoseTree.v)).

- [Nested mutual recursion](examples/Examples.nested_mut_rec.html): structural mutual and nested recursion
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/nested_mut_rec.v)).

- [Accumulators](examples/Examples.accumulator.html): defining and proving
  programs using accumulators, with well-founded recursion
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/accumulator.v)).

- [Mutual well-founded recursion](examples/Examples.mutualwfrec.html):
  representing mutually recursive well-founded definitions using
  dependent pattern-matching
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/mutualwfrec.v)).

- [General recursion](examples/Examples.general_recursion.html): working with
  general recursive functions, without worrying about termination proofs
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/general_recursion.v)).

- [Higher-order recursion](examples/Examples.ho_finite_branching.html):
  working with higher-order recursion using structural or well-founded
  recursion, here on finitely branching trees as functions from `fin n`.
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/ho_finite_branching.v)).

- [Bove Capretta](examples/Examples.bove_capretta.html): using the
  improved Bove-Cappreta method (not requiring induction-recursion) to
  prove termination of McCarthy's f91.
  ([source](https://raw.githubusercontent.com/rocq-prover/equations/refs/heads/main/examples/bove_capretta.v)).
