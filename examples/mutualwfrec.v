(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations.Prop Require Import Equations.
From Stdlib Require Import List Syntax Arith Lia.
From Stdlib Require Import List Wellfounded.
Import ListNotations.
(* end hide *)
(** * Mutual well-founded recursion using dependent pattern-matching

  We present a simple encoding of mutual recursion through the use of
  dependent pattern-matching on a GADT-like representation of the functions
  prototypes or just using strong elimination on an enumerated type.
  We use a simple toy measure here to justify termination,
  but more elaborate well-founded relations can be used as well.
 *)

Set Equations Transparent.

Import Sigma_Notations.

(** We first declare the prototypes ouf our mutual definitions. *)
Set Universe Polymorphism.
Inductive ty : forall (A : Type) (P : A -> Type), Set :=
| ty0 : ty nat (fun _ => nat)
| ty1 : ty (list nat) (fun _ => bool).
Derive Signature NoConfusion for ty.

(** Our measure is simple, just the natural number or length of the list argument. *)
Equations measure : (Σ A P (_ : A), ty A P) -> nat :=
  measure (_, _, a, ty0) => a;
  measure (_, _, a, ty1) => length a.

Definition rel := Program.Wf.MR lt measure.

#[local] Instance: WellFounded rel.
Proof.
  red. apply Wf.measure_wf. apply Wf_nat.lt_wf.
Defined.

Definition pack {A} {P} (x : A) (t : ty A P) := (A, P, x, t) : (Σ A P (_ : A), ty A P).

(** We define the function by recursion on the abstract packed argument.
    Using dependent pattern matching, the clauses for [ty0] refine the argument
    and return type to [nat] and similarly for [ty1], we can hence do pattern-matching
    as usual on each separate definition. *)
Equations? double_fn {A} {P} (t : ty A P) (x : A) : P x by wf (pack x t) rel :=
  double_fn ty0 n := n + 0;
  double_fn ty1 nil := true;
  double_fn ty1 (x :: xs) := 0 <? length xs + double_fn ty0 (length xs).
(** It is easily shown terminating in this case. *)
Proof. red. red. cbn. auto with arith. Qed.

(** We can define auxilliary definition to select the functions we want and express unfolding
    lemmas in terms of these abbreviations. *)
Definition fn0 := double_fn ty0.
Definition fn1 := double_fn ty1.

Lemma fn0_unfold n : fn0 n = n + 0.
Proof.
  unfold fn0. now simp double_fn.
Qed.

Lemma fn1_unfold l : fn1 l = match l with nil => true | x :: xs => 0 <? length xs + fn0 (length xs) end.
Proof.
  unfold fn1; simp double_fn. destruct l; now simp double_fn.
Qed.

(** ** Well-founded nested recursion

  The following example uses just dependent elimination on a finite type (booleans)
  and shows that this also applies to nested recursive definitions. *)

(** We first define [list_size] and rose trees *)

Section list_size.
  Context {A : Type} (f : A -> nat).
  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons x xs) := S (f x + list_size xs).

End list_size.
Transparent list_size.

Section RoseMut.
  Context {A : Set}.

  Scheme All for list.
  Inductive t : Set :=
  | leaf (a : A) : t
  | node (l : list t) : t.
  Derive NoConfusion for t.

  Equations size (r : t) : nat :=
  size (leaf _) := 0;
  size (node l) := S (list_size size l).

  (** An alternative way to define mutual definitions on nested types *)
  Equations mutmeasure (b : bool) (arg : if b then t else list t) : nat :=
  mutmeasure true t := size t;
  mutmeasure false lt := list_size size lt.

  (** The argument and return type depend on the function label ([true] or [false] here)
      and any well-founded recursive call is allowed. *)
  Equations? elements (b : bool) (x : if b then t else list t) : if b then list A else list A
    by wf (mutmeasure b x) lt :=
  elements true (leaf a) := [a];
  elements true (node l) := elements false l;
  elements false nil := nil;
  elements false (cons t ts) := elements true t ++ elements false ts.
  Proof. all:lia. Qed.

  (** Dependent return types are trickier but possible: *)
  Equations? elements_dep (b : bool) (x : if b then t else list t) :
    (if b as b' return (if b' then t else list t) -> Set then fun x : t => list A else fun x : list t => list A) x
    by wf (mutmeasure b x) lt :=
  elements_dep true (leaf a) := [a];
  elements_dep true (node l) := elements_dep false l;
  elements_dep false nil := nil;
  elements_dep false (cons t ts) := elements_dep true t ++ elements_dep false ts.
  Proof. all:lia. Qed.

End RoseMut.
