(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

(** This exports tactics *)

Set Warnings "-notation-overridden".
From Equations Require Export Init Signature.
From Equations Require Import CoreTactics.
From Equations.HoTT Require Export Logic Classes.
From Equations.HoTT Require Import WellFounded.
From Equations.HoTT Require Import DepElim EqDec Constants.
From Equations.HoTT Require Export EqDecInstances NoConfusion.
From Equations.HoTT Require Import Subterm.
From Equations.HoTT Require Export Tactics FunctionalInduction. (* funelim tactic *)

Global Obligation Tactic := Equations.CoreTactics.equations_simpl.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation simp rec_decision.

Export EquationsNotations.
