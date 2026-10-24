(** The [dependent-elimination-patterns] warning suggests, as a quick-fix, the patterns
    inferred by [dependent elimination x]. The suggested calls are replayed below. *)

From Equations.Prop Require Import Equations.
Set Warnings "dependent-elimination-patterns".

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).
Arguments vnil {A}. Arguments vcons {A} _ _ _.
Derive Signature NoConfusion NoConfusionHom for vec.

(* Impossible branches are omitted, and forced variables keep their names *)
Goal forall A n (v : vec A (S n)), v = v.
Proof. intros. dependent elimination v. change (vcons a n v = vcons a n v). reflexivity. Qed.
Goal forall A n (v : vec A (S n)), v = v.
Proof. intros. dependent elimination v as [vcons a n v]. reflexivity. Qed.

Goal forall A n (v : vec A n), v = v.
Proof. intros. dependent elimination v. all: reflexivity. Qed.
Goal forall A n (v : vec A n), v = v.
Proof. intros. dependent elimination v as [vnil | vcons a n0 v]. all: reflexivity. Qed.

(* Implicit constructor arguments are made explicit *)
Inductive ivec (A : Type) : nat -> Type :=
| inil : ivec A 0
| icons {n} : A -> ivec A n -> ivec A (S n).
Arguments inil {A}. Arguments icons {A n} _ _.
Derive Signature NoConfusion NoConfusionHom for ivec.

Goal forall A n (v : ivec A (S n)), v = v.
Proof. intros. dependent elimination v. reflexivity. Qed.
Goal forall A n (v : ivec A (S n)), v = v.
Proof. intros. dependent elimination v as [@icons n a i]. reflexivity. Qed.

(* Inaccessible arguments become wildcards *)
Inductive le : nat -> nat -> Prop :=
| le_n n : le n n
| le_S n m : le n m -> le n (S m).
Derive Signature for le.

Goal forall n m, le n (S m) -> True.
Proof. intros n m H. dependent elimination H. all: exact I. Qed.
Goal forall n m, le n (S m) -> True.
Proof. intros n m H. dependent elimination H as [le_n _ | le_S n m l]. all: exact I. Qed.
