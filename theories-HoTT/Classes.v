(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Init CoreTactics.
Set Warnings "-notation-overridden".
From HoTT Require Import Basics.Trunc HSet.
From Equations.HoTT Require Import Logic Relation Relation_Properties WellFounded.

Set Universe Polymorphism.

(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

Class WellFounded {A : Type} (R : Relation A) :=
  wellfounded : well_founded R.

(** This class contains no-cyclicity proofs.
    They can be derived from well-foundedness proofs for example.
 *)

(** The proofs of [NoCycle] can be arbitrarily large, it doesn't
    actually matter in the sense that they are used to prove
    absurdity. *)

(* Cumulative *)
Class NoCyclePackage@{i|} (A : Type@{i}) :=
  { NoCycle : A -> A -> Type@{i};
    noCycle : forall {a b}, NoCycle a b -> (a = b -> Empty) }.

(** These lemmas explains how to apply it during simplification. *)

(** We always generate a goal of the form [NoCycle x C[x]], using either
    the left or right versions of the following lemma. *)

Lemma apply_noCycle_left@{i j|} {A : Type@{i}} {noconf : NoCyclePackage A}
      (p q : A) {B : p = q -> Type@{j}} :
  NoCycle@{i} p q -> (forall H : p = q, B H).
Proof.
  intros noc eq. destruct (noCycle noc eq).
Defined.

Lemma apply_noCycle_right@{i j|} {A : Type@{i}} {noconf : NoCyclePackage A}
      (p q : A) {B : p = q -> Type@{j}} :
  NoCycle q p -> (forall H : p = q, B H).
Proof.
  intros noc eq. destruct (noCycle noc (inverse eq)).
Defined.
(* Extraction Inline apply_noCycle_left apply_noCycle_right. *)

(** NoCycle can be decided using the well-founded subterm relation. *)

Definition NoCycle_WellFounded {A} (R : Relation A) (wfR : WellFounded R) : NoCyclePackage A :=
  {| NoCycle := R;
     noCycle := WellFounded.well_founded_irreflexive (wfR:=wfR) |}.
#[export]
Existing Instance NoCycle_WellFounded.

#[export] Hint Extern 30 (@NoCycle ?A (NoCycle_WellFounded ?R ?wfr) _ _) =>
  hnf; typeclasses eauto with subterm_relation : typeclass_instances.

(** The NoConfusionPackage class provides a method for solving injectivity and discrimination
    of constructors, represented by an equality on an inductive type [I]. The type of [noConfusion]
    should be of the form [ Π Δ, (x y : I Δ) (x = y) -> NoConfusion x y ], where
   [NoConfusion x y] for constructor-headed [x] and [y] will give equality of their arguments
   or the absurd proposition in case of conflict.
   This gives a general method for simplifying by discrimination or injectivity of constructors.

   Some actual instances are defined later in the file using the more primitive [discriminate] and
   [injection] tactics on which we can always fall back.
   *)

Cumulative Class NoConfusionPackage@{i} (A : Type@{i}) := {
  NoConfusion : A -> A -> Type@{i};
  noConfusion : forall {a b}, NoConfusion a b -> a = b;
  noConfusion_inv : forall {a b}, a = b -> NoConfusion a b;
  noConfusion_sect : forall {a b} (e : NoConfusion a b), noConfusion_inv (noConfusion e) = e;
  noConfusion_retr : forall {a b} (e : a = b), (noConfusion (noConfusion_inv e)) = e;
}.

(** This lemma explains how to apply it during simplification. *)

Lemma apply_noConfusion@{i j|} {A : Type@{i}} {noconf : NoConfusionPackage A}
      (p q : A) {B : p = q -> Type@{j}} :
  (forall e : NoConfusion p q, B (noConfusion e)) -> (forall e : p = q, B e).
Proof.
  intros. generalize (noConfusion_retr e). destruct e.
  intros eq. destruct eq. apply X.
Defined.
(* Extraction Inline apply_noConfusion. *)

(** Classes for types with UIP or decidable equality.  *)

Class UIP@{i|} (A : Type@{i}) := uip : forall {x y : A} (e e' : x = y), e = e'.

#[export]
Instance IsHSet_UIP (A : Type) (H : IsHSet A) : UIP A.
Proof.
  apply axiomK_hset in H. intros x y e e'.
  red in H. destruct e'. apply H.
Defined.

(* By truncation, we also get those, we keep a single instance for HSet *)
Example IsHProp_UIP (A : Type) (H : IsHProp A) : UIP A := _.
Example Contr_UIP (A : Type) (H : Contr A) : UIP A := _.

Definition dec_eq {A} (x y : A) : Type := (x = y) + (x <> y).

Class EqDec@{i} (A : Type@{i}) := eq_dec : forall x y : A, sum@{i i} (x = y) (x = y -> Empty).

Class EqDecPoint (A : Type) (x : A) := eq_dec_point : forall y : A, (x = y) + (x <> y).

#[export]
Instance EqDec_EqDecPoint A `(EqDec A) (x : A) : EqDecPoint A x := eq_dec x.

(** For treating impossible cases. Equations corresponding to impossible
   calls form instances of [ImpossibleCall (f args)]. *)

Class ImpossibleCall {A : Type} (a : A) : Type :=
  is_impossible_call : Empty.

(** We have a trivial elimination operator for impossible calls. *)

Definition elim_impossible_call {A} (a : A) {imp : ImpossibleCall a} (P : A -> Type) : P a :=
  match is_impossible_call with end.

(** The tactic tries to find a call of [f] and eliminate it. *)

Ltac impossible_call f := on_call f ltac:(fun t => apply (elim_impossible_call t)).

(** The [FunctionalInduction f] typeclass is meant to register functional induction
   principles associated to a function [f]. Such principles are automatically
   generated for definitions made using [Equations]. *)

Polymorphic
Class FunctionalInduction {A : Type} (f : A) :=
  { fun_ind_prf_ty : Type; fun_ind_prf : fun_ind_prf_ty }.

Register FunctionalInduction as equations.funind.class.

(** The [FunctionalElimination f] class declares elimination principles produced
   from the functional induction principle for [f] to be used directly to eliminate
   a call to [f]. This is the preferred method of proving results about a function.
   [n] is the number of binders for parameters, predicates and methods of the
   eliminator.
   *)

Polymorphic
Class FunctionalElimination {A : Type} (f : A) (fun_elim_ty : Type) (n : nat) :=
  fun_elim : fun_elim_ty.

Register FunctionalElimination as equations.funelim.class.
