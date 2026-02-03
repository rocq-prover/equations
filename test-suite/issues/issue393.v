From Equations.Prop Require Import Equations.

From Stdlib Require Import List.

Inductive In {X} (x : X) : list X -> Type :=
| here {xs} : In x (x :: xs)
| there {y xs} : In x xs -> In x (y :: xs).
Derive Signature NoConfusion for In.
Notation " x ∈ xs " := (In x xs) (at level 70, xs at level 10).
Arguments here {X x xs}.
Arguments there {X x y xs} _.
Check (there here) : 26 ∈ (43 :: 26 :: 76 :: nil).

(* Does rocq-equations mistake variable names sometimes? *)

Equations repl {A} (R : list A) prev (idx : prev ∈ R) (next : A) : list A :=
  repl (X :: XS) X here         next := next :: XS;
  repl (X :: XS) prev (there idx') next := X :: (repl XS prev idx' next).

Equations repl' {A} (R : list A) {prev} (idx : prev ∈ R) (next : A) : list A :=
  repl' (X :: XS) here         next := next :: XS;
  repl' (X :: XS) (there idx') next := X :: (repl' XS idx' next).
