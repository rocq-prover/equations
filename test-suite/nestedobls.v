(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
Set Implicit Arguments.
Unset Strict Implicit.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Equations.Prop Require Import Equations.

From Stdlib Require Import Wellfounded Relation_Definitions.
From Stdlib Require Import Relation_Operators Lexicographic_Product Wf_nat.
Unset Implicit Arguments.
From Stdlib Require Import Program.

Equations? test (n : nat) (pre : n >= 0 ) : { n' : nat | n' <= n }
 by wf n lt :=
test 0 p := exist _ 0 _;
test (S n) p with test n _ => {
                | exist _ 0 _ := exist _ 0 _;
                | exist _ (S n') p' with test n' _ := {
                                                  | exist _ k p'' := exist _ k _ } }.
Proof. all:(auto with arith; lia). Defined.

Module Bug.
  (* FIXME: shrink obligations so that they can apply during induction principle generation *)
  Equations? (noind) test' (n : { n : nat | n >= 0 }) : { n' : nat | n' <= `n }
  by wf (proj1_sig n) lt :=
  test' (exist _ n p) with n := {
  | 0 := exist _ 0 _;
  | S n' with test' (exist _ n' _) => {
                  | exist _ 0 _ := exist _ 0 _;
                  | exist _ (S n'') p' with test' (exist _ n'' _) := {
                      | exist _ k p'' := exist _ k _ } } }.
  Proof. all:(clear test'; unfold MR; simpl; auto with arith). lia. Defined.

End Bug.
