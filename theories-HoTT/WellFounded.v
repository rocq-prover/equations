Set Warnings "-notation-overridden".
From Equations Require Import Init CoreTactics.
From Equations.HoTT Require Import Logic Relation Relation_Properties.
From HoTT Require Import Basics.Tactics.

Set Universe Polymorphism.
Import Sigma_Notations.

(** Well-founded relations in Type *)

Section Acc.
  Universes i j.
  Context {A : Type@{i}} (R : Relation@{i j} A).

  Cumulative Inductive Acc (x : A) : Type :=
  | Acc_intro : (forall y, R y x -> Acc y) -> Acc x.

  Definition Acc_inv {x} (H : Acc x) : forall y, R y x -> Acc y.
  Proof. intros y Hy. destruct H. exact (a _ Hy). Defined.

  Definition well_founded := forall x, Acc x.

  Context (P : A -> Type).
  Context (step : forall x : A, (forall y : A, R y x -> P y) -> P x).

  Fixpoint Fix_F (x : A) (a : Acc x) : P x :=
    step x (fun y r => Fix_F y (Acc_inv a y r)).

End Acc.

Lemma Acc_prop `{Funext} {A} (R : Relation A) i (x y : Acc R i) : x = y.
Proof.
  revert y.
  induction x as [y Accy IHy].
  intros [Accy']. apply ap.
  funext H'. funext H''.
  apply IHy.
Qed.

Section FixWf.
  Context {A R} (WF : @well_founded A R).
  Context (P : A -> Type).
  Context (step : forall x : A, (forall y : A, R y x -> P y) -> P x).

  Definition Fix (x : A) : P x :=
    Fix_F R P step x (WF x).

  Lemma Fix_F_eq :
   forall (x:A) (r:Acc R x),
     step _ (fun (y:A) (p:R y x) => Fix_F R P step y (Acc_inv R r _ p)) = Fix_F R P step x r.
  Proof.
    destruct r; reflexivity.
  Defined.

  Hypothesis
    step_ext :
      forall (x:A) (f g:forall y:A, R y x -> P y),
        (forall (y:A) (p:R y x), f y p = g y p) -> step _ f = step _ g.

  Lemma Fix_step_inv : forall (x:A) (r s:Acc R x), Fix_F R P step _ r = Fix_F R P step _ s.
  Proof.
   intro x; induction (WF x); intros.
   rewrite <- (Fix_F_eq _ r); rewrite <- (Fix_F_eq _ s); intros.
   apply step_ext; auto.
  Defined.

  Lemma Fix_eq : forall x:A, Fix x = step _ (fun (y:A) (p:R y x) => Fix y).
  Proof.
   intro x; unfold Fix.
   rewrite <- Fix_F_eq.
   apply step_ext; intros.
   apply Fix_step_inv.
  Defined.

End FixWf.

Lemma well_founded_irreflexive {A} {R : Relation A} {wfR : well_founded R} :
  forall x y : A, R x y -> x = y -> Empty.
Proof.
  intros x y Ryy. intros e. destruct e. red in wfR.
  induction (wfR x) as [y accy IHy].
  apply (IHy _ Ryy Ryy).
Qed.

Lemma well_founded_antisym@{i j} {A : Type@{i}} {R : Relation@{i j} A}{wfR : well_founded R} :
  forall x y : A, R x y -> R y x -> Empty.
Proof.
  intros x y Rxy Ryx. red in wfR.
  induction (wfR y) as [y accy IHy] in x, Rxy, Ryx.
  specialize (IHy _ Rxy). apply (IHy _ Ryx Rxy).
Qed.

Section Wf_Transitive_Closure.

  (** Original author: Bruno Barras, adapted to Type *)
  Context {A : Type} (R : Relation A).

  Notation trans_clos := (trans_clos R).

  Lemma incl_trans_clos : inclusion R trans_clos.
    red; auto with Relations.
  Defined.

  Lemma Acc_trans_clos : forall x:A, Acc R x -> Acc trans_clos x.
    induction 1 as [x0 _ H1].
    apply Acc_intro.
    intros y H2.
    induction H2; auto with Relations.
    apply Acc_inv with y; auto with Relations.
  Defined.

  Hint Resolve Acc_trans_clos : core.

  Lemma Acc_inv_trans : forall x y:A, trans_clos y x -> Acc R x -> Acc R y.
  Proof.
    induction 1 as [| x y]; auto with Relations.
    intro; apply Acc_inv with y; assumption.
  Defined.

  Theorem wf_trans_clos : well_founded R -> well_founded trans_clos.
  Proof.
    unfold well_founded; auto with Relations.
  Defined.

End Wf_Transitive_Closure.

(** Author: Bruno Barras *)

Section Inverse_Image.

  Context {A B : Type} (R : Relation B) (f : A -> B).

  Definition inverse_image := fun x y => R (f x) (f y).

  Remark Acc_lemma : forall y : B, Acc R y -> forall x : A, y = f x -> Acc inverse_image x.
  Proof.
    induction 1 as [y _ IHAcc]; intros x H.
    apply Acc_intro; intros y0 H1.
    apply (IHAcc (f y0)); try trivial.
    apply inverse in H. destruct H; trivial.
  Defined.

  Lemma Acc_inverse_image : forall x:A, Acc R (f x) -> Acc inverse_image x.
  Proof.
    intros; apply (Acc_lemma (f x)); trivial.
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

