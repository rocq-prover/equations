(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Warnings "-notation-overridden".
From Equations Require Import CoreTactics.
From Equations.HoTT Require Import Logic DepElim Subterm EqDec WellFounded FunctionalInduction.

Ltac Equations.Init.simpl_equations ::= DepElim.simpl_equations.
Ltac Equations.Init.simplify_equalities ::= DepElim.simplify_dep_elim.

Ltac Equations.Init.depelim H ::= dependent elimination H; cbn in *.
Ltac Equations.Init.depind H ::= DepElim.depind H.
Ltac Equations.Init.simp_IHs_tac ::= FunctionalInduction.simplify_IHs_call.
Ltac Equations.Init.funelim_constr_as H H' tac ::= FunctionalInduction.funelim_constr_as H H' tac.
Ltac Equations.Init.apply_funelim H ::= FunctionalInduction.apply_funelim H.

Ltac Equations.Init.noconf H ::= DepElim.noconf H.

Create HintDb solve_subterm discriminated.

#[export] Hint Extern 4 (_ = _) => reflexivity : solve_subterm.
#[export] Hint Extern 10 => eapply_hyp : solve_subterm.

Ltac solve_subterm := intros;
  apply WellFounded.wf_trans_clos;
  red; intros; simp_sigmas; on_last_hyp ltac:(fun H => depind H); constructor;
  intros; simp_sigmas; on_last_hyp ltac:(fun HR => Equations.Init.depelim HR);
  simplify_dep_elim; try typeclasses eauto with solve_subterm.

Ltac Equations.Init.solve_subterm ::= solve_subterm.
Ltac Equations.Init.unfold_recursor ::= Subterm.unfold_recursor.
Ltac Equations.Init.unfold_recursor_ext ::= Subterm.unfold_recursor_ext.

Ltac solve_noconf_inv_eq a b :=
  destruct_sigma a; destruct_sigma b;
  do_case a; intros; depelim b; simpl in * |-;
  on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
  solve [constructor].

Ltac solve_noconf_inv := intros;
  match goal with
  | |- (?f ?a ?b _) = _ => solve_noconf_inv_eq a b
  | |- ?R ?a ?b => destruct_sigma a; destruct_sigma b;
                   do_case a ; intros; depelim b; simpl in * |-;
                 on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
                 solve [constructor]
  end.

Ltac solve_noconf_prf :=
  intros;
  (* Subtitute a = b *)
  on_last_hyp ltac:(fun id => destruct id) ;
  (* Destruct the inductive object a *)
  on_last_hyp ltac:(fun id => destruct_sigma id; do_case id; intros) ;
  simpl; constructor.

Ltac solve_noconf := simpl; intros;
    match goal with
    | [ H : _ = _ |- _ ] => try solve_noconf_prf
    | [ |- _ = _ ] => try solve_noconf_inv
    end.

Ltac solve_noconf_hom_inv_eq a b :=
  destruct_sigma a; destruct_sigma b;
  do_case a; intros; depelim b; simpl in * |-;
  on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || depelim id);
  solve [constructor || simpl_equations; constructor].

Ltac solve_noconf_hom_inv := intros;
  match goal with
  | |- (?f ?a ?b _) = _ => solve_noconf_hom_inv_eq a b
  | |- ?R ?a ?b =>
    destruct_sigma a; destruct_sigma b;
    do_case a ; intros; depelim b; simpl in * |-;
    on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || depelim id);
    solve [constructor || simpl_equations; constructor]
  end.

Ltac solve_noconf_hom_inv_equiv :=
  intros;
  (* Subtitute a = b *)
  on_last_hyp ltac:(fun id => do_case id) ;
  (* Destruct the inductive object a using dependent elimination
     to handle UIP cases. *)
  on_last_hyp ltac:(fun id => destruct_sigma id; depelim id) ;
  simpl; simpl_equations; constructor.

Ltac solve_noconf_hom := simpl; intros;
    match goal with
      [ H : _ = _ |- _ = _ ] => try solve_noconf_hom_inv_equiv
    | [ H : _ = _ |- _ ] => try solve_noconf_prf
    | [ |- _ = _ ] => try solve_noconf_hom_inv
    end.

Ltac Equations.Init.solve_noconf ::= solve_noconf.
Ltac Equations.Init.solve_noconf_hom ::= solve_noconf_hom.
