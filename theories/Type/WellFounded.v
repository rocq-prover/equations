Set Warnings "-notation-overridden".
From Stdlib Require Import Extraction CRelationClasses.
From Equations Require Import Init CoreTactics.
From Equations.Type Require Import Logic FunctionalExtensionality Relation Relation_Properties.

Set Universe Polymorphism.
Import Id_Notations.
Import Sigma_Notations.

(** Well-founded relations in Type *)

Section Acc.
  Universes i j.
  Context {A : Type@{i}} (R : relation@{i j} A).

  Cumulative
  Inductive Acc (x : A) : Type@{max(i,j)} :=
  | Acc_intro : (forall y, R y x -> Acc y) -> Acc x.

  Definition Acc_inv {x} (H : Acc x) : forall y, R y x -> Acc y.
  Proof. intros y Hy. destruct H. exact (a _ Hy). Defined.

  Lemma Acc_prop i (x y : Acc i) : x = y.
  Proof.
    revert y.
    induction x as [y Accy IHy].
    intros [Accy']. apply ap.
    apply funext. intros H.
    apply funext. intros H'.
    apply IHy.
  Qed.

  Definition well_founded := forall x, Acc x.

  Context (P : A -> Type).
  Context (step : forall x : A, (forall y : A, R y x -> P y) -> P x).

  Fixpoint Fix_F (x : A) (a : Acc x) : P x :=
    step x (fun y r => Fix_F y (Acc_inv a y r)).

End Acc.

Section FixWf.
  Context {A R} (WF : @well_founded A R).
  Context (P : A -> Type).
  Context (step : forall x : A, (forall y : A, R y x -> P y) -> P x).

  Definition Fix (x : A) : P x :=
    Fix_F R P step x (WF x).
End FixWf.

Lemma well_founded_irreflexive {A} {R : relation A} {wfR : well_founded R} :
  forall x y : A, R x y -> x = y -> Empty.
Proof.
  intros x y Ryy. intros e. destruct e. red in wfR.
  induction (wfR x) as [y accy IHy].
  apply (IHy _ Ryy Ryy).
Qed.

Lemma well_founded_antisym@{i j} {A : Type@{i}} {R : relation@{i j} A}{wfR : well_founded R} :
  forall x y : A, R x y -> R y x -> Empty.
Proof.
  intros x y Rxy Ryx. red in wfR.
  induction (wfR y) as [y accy IHy] in x, Rxy, Ryx.
  specialize (IHy _ Rxy). apply (IHy _ Ryx Rxy).
Qed.

Section Wf_Transitive_Closure.

  (** Original author: Bruno Barras, adapted to Type *)
  Context {A : Type} (R : relation A).

  Abbreviation trans_clos := (trans_clos R).

  Lemma incl_trans_clos : inclusion R trans_clos.
  Proof.
    red; auto with relations.
  Defined.

  Lemma Acc_trans_clos : forall x:A, Acc R x -> Acc trans_clos x.
  Proof.
    induction 1 as [x0 _ H1].
    apply Acc_intro.
    intros y H2.
    induction H2; auto with relations.
    apply Acc_inv with y; auto with relations.
  Defined.

  Hint Resolve Acc_trans_clos : core.

  Lemma Acc_inv_trans : forall x y:A, trans_clos y x -> Acc R x -> Acc R y.
  Proof.
    induction 1 as [| x y]; auto with relations.
    intro; apply Acc_inv with y; assumption.
  Defined.

  Theorem wf_trans_clos : well_founded R -> well_founded trans_clos.
  Proof.
    unfold well_founded; auto with relations.
  Defined.

End Wf_Transitive_Closure.

(** Author: Bruno Barras *)

Section Inverse_Image.

  Context {A B : Type} (R : relation B) (f : A -> B).

  Definition inverse_image := fun x y => R (f x) (f y).

  Remark Acc_lemma : forall y : B, Acc R y -> forall x : A, y = f x -> Acc inverse_image x.
  Proof.
    induction 1 as [y _ IHAcc]; intros x H.
    apply Acc_intro; intros y0 H1.
    apply (IHAcc (f y0)); try trivial.
    apply id_sym in H. destruct H; trivial. constructor.
  Defined.

  Lemma Acc_inverse_image : forall x:A, Acc R (f x) -> Acc inverse_image x.
  Proof.
    intros; apply (Acc_lemma (f x)); trivial. constructor.
  Defined.

  Theorem wf_inverse_image : well_founded R -> well_founded inverse_image.
  Proof.
    red; intros; apply Acc_inverse_image; auto.
  Defined.

  (* Variable F : A -> B -> Type. *)
  (* Let RoF (x y:A) := *)
  (*   exists2 b : B, F x b & (forall c:B, F y c -> R b c). *)

  (* Lemma Acc_inverse_rel : forall b:B, Acc R b -> forall x:A, F x b -> Acc RoF x. *)
  (* Proof. *)
  (*   induction 1 as [x _ IHAcc]; intros x0 H2. *)
  (*   constructor; intros y H3. *)
  (*   destruct H3. *)
  (*   apply (IHAcc x1); auto. *)
  (* Qed. *)


  (* Theorem wf_inverse_rel : well_founded R -> well_founded RoF. *)
  (* Proof. *)
  (*   red; constructor; intros. *)
  (*   case H0; intros. *)
  (*   apply (Acc_inverse_rel x); auto. *)
  (* Qed. *)

End Inverse_Image.

