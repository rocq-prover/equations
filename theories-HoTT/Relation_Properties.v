(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(** * Some properties of the operators on relations                     *)
(************************************************************************)
(** * Initial version by Bruno Barras                                   *)
(************************************************************************)

Set Warnings "-notation-overridden".

From Equations Require Import Init.
From Equations.HoTT Require Import Logic Relation.

Import Sigma_Notations.

(** Synonyms *)

Definition subrelation {A} (R S : Relation A) :=
  forall x y, R x y -> S x y.

Class Equivalence {A} (R : Relation A) :=
  { Equivalence_Reflexive :: Reflexive R | 2 ;
    Equivalence_Symmetric :: Symmetric R | 2 ;
    Equivalence_Transitive :: Transitive R | 2 }.

Notation inclusion R R' := (subrelation R R').

#[export] Hint Constructors sum : Relations.

Section Properties.

  Context{A : Type}.
  Variable R : Relation A.

  Section Clos_Refl_Trans.

    Local Notation "R *" := (clos_refl_trans R)
      (at level 8, no associativity, format "R *").

    (** Correctness of the reflexive-transitive closure operator *)

    Lemma clos_rt_is_preorder : PreOrder R*.
    Proof.
      constructor.
      - exact (rt_refl R).
      - exact (rt_trans R).
    Defined.

    (** Idempotency of the reflexive-transitive closure operator *)

    Lemma clos_rt_idempotent : subrelation (R*)* R*.
    Proof.
      red.
      induction 1; auto with Relations.
      intros.
      apply rt_trans with y; auto with Relations.
    Defined.

  End Clos_Refl_Trans.

  Section Clos_Refl_Sym_Trans.

    (** Reflexive-transitive closure is included in the
        reflexive-symmetric-transitive closure *)

    Lemma clos_rt_clos_rst :
      subrelation (clos_refl_trans R) (clos_refl_sym_trans R).
    Proof.
      red.
      induction 1; auto with Relations.
      apply rst_trans with y; auto with Relations.
    Defined.

    (** Reflexive closure is included in the
        reflexive-transitive closure *)

    Lemma clos_r_clos_rt :
      inclusion (clos_refl R) (clos_refl_trans R).
    Proof.
      induction 1 as [? ?| ].
      - constructor; auto.
      - constructor 2.
    Defined.

    Lemma clos_rt_t : forall x y z,
      clos_refl_trans R x y -> trans_clos R y z ->
      trans_clos R x z.
    Proof.
      induction 1 as [b d H1|b|a b d H1 H2 IH1 IH2]; auto.
      intro H. apply t_trans with (y:=d); auto.
      constructor. auto.
    Defined.

    (** Correctness of the reflexive-symmetric-transitive closure *)

    Lemma clos_rst_is_equiv : Equivalence (clos_refl_sym_trans R).
    Proof.
      constructor.
      - exact (rst_refl R).
      - exact (rst_sym R).
      - exact (rst_trans R).
    Defined.

    (** Idempotency of the reflexive-symmetric-transitive closure operator *)

    Lemma clos_rst_idempotent :
      inclusion (clos_refl_sym_trans (clos_refl_sym_trans R))
      (clos_refl_sym_trans R).
    Proof.
      red.
      induction 1; auto with Relations.
      apply rst_trans with y; auto with Relations.
    Defined.

  End Clos_Refl_Sym_Trans.

  Section Equivalences.

  (** *** Equivalences between the different definition of the reflexive,
      symmetric, transitive closures *)

  (** *** Contributed by P. Castéran *)

    (** Direct transitive closure vs left-step extension *)

    Lemma clos_t1n_trans : forall x y, trans_clos_1n R x y -> trans_clos R x y.
    Proof.
     induction 1.
     - left; assumption.
     - right with y; auto.
       left; auto.
    Defined.

    Lemma trans_clos_t1n : forall x y, trans_clos R x y -> trans_clos_1n R x y.
    Proof.
      induction 1.
      - left; assumption.
      - generalize IHX2; clear IHX2; induction IHX1.
        -- right with y; auto.
        -- right with y; auto.
           eapply IHIHX1; auto.
           apply clos_t1n_trans; auto.
    Defined.

    Lemma trans_clos_t1n_iff : forall x y,
        trans_clos R x y <-> trans_clos_1n R x y.
    Proof.
      intros x y.
      split.
      - apply (trans_clos_t1n x y).
      - apply (clos_t1n_trans x y).
    Defined.

    (** Direct transitive closure vs right-step extension *)

    Lemma clos_tn1_trans : forall x y, trans_clos_n1 R x y -> trans_clos R x y.
    Proof.
      induction 1.
      - left; assumption.
      - right with y; auto.
        left; assumption.
    Defined.

    Lemma trans_clos_tn1 :  forall x y, trans_clos R x y -> trans_clos_n1 R x y.
    Proof.
      induction 1.
      - left; assumption.
      - elim IHX2.
        -- intro y0; right with y; auto.
        -- intros. right with y0; auto.
    Defined.

    Lemma trans_clos_tn1_iff : forall x y,
        trans_clos R x y <-> trans_clos_n1 R x y.
    Proof.
      split.
      - apply trans_clos_tn1.
      - apply clos_tn1_trans.
    Defined.

    (** Direct reflexive-transitive closure is equivalent to
        transitivity by left-step extension *)

    Lemma clos_rt1n_step : forall x y, R x y -> clos_refl_trans_1n R x y.
    Proof.
      intros x y H.
      right with y;[assumption|left].
    Defined.

    Lemma clos_rtn1_step : forall x y, R x y -> clos_refl_trans_n1 R x y.
    Proof.
      intros x y H.
      right with x;[assumption|left].
    Defined.

    Lemma clos_rt1n_rt : forall x y,
        clos_refl_trans_1n R x y -> clos_refl_trans R x y.
    Proof.
      induction 1.
      - constructor 2.
      - constructor 3 with y; auto.
        constructor 1; auto.
    Defined.

    Lemma clos_rt_rt1n : forall x y,
        clos_refl_trans R x y -> clos_refl_trans_1n R x y.
    Proof.
      induction 1.
      - apply clos_rt1n_step; assumption.
      - left.
      - generalize IHX2; clear IHX2;
          induction IHX1; auto.
        right with y; auto.
        eapply IHIHX1; auto.
        apply clos_rt1n_rt; auto.
    Defined.

    Lemma clos_rt_rt1n_iff : forall x y,
      clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
    Proof.
      split.
      - apply clos_rt_rt1n.
      - apply clos_rt1n_rt.
    Defined.

    (** Direct reflexive-transitive closure is equivalent to
        transitivity by right-step extension *)

    Lemma clos_rtn1_rt : forall x y,
        clos_refl_trans_n1 R x y -> clos_refl_trans R x y.
    Proof.
      induction 1.
      - constructor 2.
      - constructor 3 with y; auto.
        constructor 1; assumption.
    Defined.

    Lemma clos_rt_rtn1 :  forall x y,
        clos_refl_trans R x y -> clos_refl_trans_n1 R x y.
    Proof.
      induction 1.
      - apply clos_rtn1_step; auto.
      - left.
      - elim IHX2; auto.
        intros.
        right with y0; auto.
    Defined.

    Lemma clos_rt_rtn1_iff : forall x y,
        clos_refl_trans R x y <-> clos_refl_trans_n1 R x y.
    Proof.
      split.
      - apply clos_rt_rtn1.
      - apply clos_rtn1_rt.
    Defined.

    (** Induction on the left transitive step *)

    Lemma clos_refl_trans_ind_left :
      forall (x:A) (P:A -> Type), P x ->
	(forall y z:A, clos_refl_trans R x y -> P y -> R y z -> P z) ->
	forall z:A, clos_refl_trans R x z -> P z.
    Proof.
      intros.
      revert X X0.
      induction X1; intros; auto with Relations.
      { apply X0 with x; auto with Relations. }
      apply IHX1_2.
      { apply IHX1_1; auto with Relations. }
      intros.
      apply X0 with y0; auto with Relations.
      apply rt_trans with y; auto with Relations.
    Defined.

    (** Induction on the right transitive step *)

    Lemma rt1n_ind_right : forall (P : A -> Type) (z:A),
      P z ->
      (forall x y, R x y -> clos_refl_trans_1n R y z -> P y -> P x) ->
      forall x, clos_refl_trans_1n R x z -> P x.
      induction 3; auto.
      apply X0 with y; auto.
    Defined.

    Lemma clos_refl_trans_ind_right : forall (P : A -> Type) (z:A),
      P z ->
      (forall x y, R x y -> P y -> clos_refl_trans R y z -> P x) ->
      forall x, clos_refl_trans R x z -> P x.
      intros P z Hz IH x Hxz.
      apply clos_rt_rt1n_iff in Hxz.
      elim Hxz using rt1n_ind_right; auto.
      clear x Hxz.
      intros x y Hxy Hyz Hy.
      apply clos_rt_rt1n_iff in Hyz.
      eauto.
    Defined.

    (** Direct reflexive-symmetric-transitive closure is equivalent to
        transitivity by symmetric left-step extension *)

    Lemma clos_rst1n_rst  : forall x y,
      clos_refl_sym_trans_1n R x y -> clos_refl_sym_trans R x y.
    Proof.
      induction 1.
      - constructor 2.
      - constructor 4 with y; auto.
        case s; [constructor 1 | constructor 3; constructor 1]; auto.
    Defined.

    Lemma clos_rst1n_trans : forall x y z, clos_refl_sym_trans_1n R x y ->
        clos_refl_sym_trans_1n R y z -> clos_refl_sym_trans_1n R x z.
      induction 1.
      - auto.
      - intros; right with y; eauto.
    Defined.

    Lemma clos_rst1n_sym : forall x y, clos_refl_sym_trans_1n R x y ->
      clos_refl_sym_trans_1n R y x.
    Proof.
      intros x y H; elim H.
      - constructor 1.
      - intros x0 y0 z D H0 H1; apply clos_rst1n_trans with y0; auto.
        right with x0.
        + destruct D; [right|left]; auto.
        + left.
    Defined.

    Lemma clos_rst_rst1n  : forall x y,
      clos_refl_sym_trans R x y -> clos_refl_sym_trans_1n R x y.
      induction 1.
      - constructor 2 with y; auto with Relations;
        constructor 1; assumption.
      - constructor 1.
      - apply clos_rst1n_sym; auto.
      - eapply clos_rst1n_trans; eauto.
    Defined.

    Lemma clos_rst_rst1n_iff : forall x y,
      clos_refl_sym_trans R x y <-> clos_refl_sym_trans_1n R x y.
    Proof.
      split.
      - apply clos_rst_rst1n.
      - apply clos_rst1n_rst.
    Defined.

    (** Direct reflexive-symmetric-transitive closure is equivalent to
        transitivity by symmetric right-step extension *)

    Lemma clos_rstn1_rst : forall x y,
      clos_refl_sym_trans_n1 R x y -> clos_refl_sym_trans R x y.
    Proof.
      induction 1.
      - constructor 2.
      - constructor 4 with y; auto.
        case s; [constructor 1 | constructor 3; constructor 1]; auto.
    Defined.

    Lemma clos_rstn1_trans : forall x y z, clos_refl_sym_trans_n1 R x y ->
      clos_refl_sym_trans_n1 R y z -> clos_refl_sym_trans_n1 R x z.
    Proof.
      intros x y z H1 H2.
      induction H2.
      - auto.
      - intros.
        right with y0; eauto.
    Defined.

    Lemma clos_rstn1_sym : forall x y, clos_refl_sym_trans_n1 R x y ->
      clos_refl_sym_trans_n1 R y x.
    Proof.
      intros x y H; elim H.
      - constructor 1.
      - intros y0 z D H0 H1. apply clos_rstn1_trans with y0; auto.
        right with z.
        + destruct D; auto with Relations.
        + left.
    Defined.

    Lemma clos_rst_rstn1 : forall x y,
      clos_refl_sym_trans R x y -> clos_refl_sym_trans_n1 R x y.
    Proof.
      induction 1.
      - constructor 2 with x; auto with Relations.
        constructor 1.
      - constructor 1.
      - apply clos_rstn1_sym; auto.
      - eapply clos_rstn1_trans; eauto.
    Defined.

    Lemma clos_rst_rstn1_iff : forall x y,
      clos_refl_sym_trans R x y <-> clos_refl_sym_trans_n1 R x y.
    Proof.
      split.
      - apply clos_rst_rstn1.
      - apply clos_rstn1_rst.
    Defined.

  End Equivalences.

  Lemma trans_clos_transp_permute : forall x y,
    transp (trans_clos R) x y <-> trans_clos (transp R) x y.
  Proof.
    split; induction 1;
    (apply t_step; assumption) || eapply t_trans; eassumption.
  Defined.

End Properties.
