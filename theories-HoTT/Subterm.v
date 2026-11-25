(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Warnings "-notation-overridden".

From Equations Require Import Init Signature.
From Equations Require Import CoreTactics.
From Equations.HoTT Require Import Logic Classes EqDec Relation WellFounded
  DepElim Constants.
From HoTT Require Import Basics.Tactics Spaces.Nat.

Set Universe Polymorphism.

Generalizable Variables A R S B.

(** The fixpoint combinator associated to a well-founded relation,
   just reusing the [WellFounded.Fix] combinator. *)

Definition FixWf `{WF:WellFounded A R} (P : A -> Type)
  (step : forall x : A, (forall y : A, R y x -> P y) -> P x) : forall x : A, P x :=
  Fix wellfounded P step.


Definition step_fn_ext {A} {R} (P : A -> Type) :=
  fun step : forall x : A, (forall y : A, R y x -> P y) -> P x =>
    forall x (f g : forall y (H : R y x), P y),
      (forall y H, f y H = g y H) ->
      step x f = step x g.

Lemma FixWf_unfold `{WF : WellFounded A R} (P : A -> Type)
      (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
      (step_ext : step_fn_ext P step) (x : A) :
  FixWf P step x = step x (fun y _ => FixWf P step y).
Proof.
  intros.
  unfold FixWf.
  rewrite WellFounded.Fix_eq.
  - apply step_ext. intros. reflexivity.
  - intros x' f g H. apply step_ext. apply H.
Defined.

Lemma FixWf_unfold_step :
  forall (A : Type) (R : Relation A) (WF : WellFounded R) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A)
    (step_ext : step_fn_ext P step)
    (step' : forall y : A, R y x -> P y),
    step' = (fun (y : A) (_ : R y x) => FixWf P step y) ->
    FixWf P step x = step x step'.
Proof.
  intros. rewrite FixWf_unfold, X.
  - reflexivity.
  - apply step_ext.
Defined.

Ltac unfold_FixWf :=
  match goal with
    |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] =>
    let step := fresh in
    set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *;
     unshelve erewrite (@FixWf_unfold_step A R WF P f x _ step idpath);
     [red; intros; simp_sigmas; red_one_eq (* Extensionality proof *)
     |hidebody step; try red_eq_lhs (* Unfold the functional *)]
  end.

Ltac unfold_recursor := unfold_FixWf.

Lemma FixWf_unfold_ext `{Funext} `{WF : WellFounded A R} (P : A -> Type)
  (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) :
  FixWf P step x = step x (fun y _ => FixWf P step y).
Proof.
  intros. unfold FixWf, Fix. destruct wellfounded.
  simpl. apply ap. funext y h. apply ap. apply Acc_prop.
Defined.

#[export] Hint Rewrite @FixWf_unfold_ext : Recursors.

Lemma FixWf_unfold_ext_step `{Funext} :
  forall (A : Type) (R : Relation A) (WF : WellFounded R) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A)
    (step' : forall y : A, R y x -> P y),
    step' = (fun (y : A) (_ : R y x) => FixWf P step y) ->
    FixWf P step x = step x step'.
Proof. intros. rewrite FixWf_unfold_ext, X. reflexivity. Defined.

#[export] Hint Rewrite @FixWf_unfold_ext_step : Recursors.

Ltac unfold_FixWf_ext :=
  match goal with
    |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] =>
    let step := fresh in
    set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *;
    eapply concat;
    [exact (@FixWf_unfold_ext_step (_ : Funext) A R WF P f x step idpath) |
     hidebody step; try red_eq_lhs (* Unfold the functional *)]
  end.

Ltac unfold_recursor_ext := unfold_FixWf_ext.

#[export] Hint Rewrite @FixWf_unfold : Recursors.

(** Inline so that we get back a term using general recursion. *)

Extraction Inline FixWf Fix Fix_F.

(** This hint database contains the constructors of every derived
   subterm relation. It is used to automatically find proofs that
   a term is a subterm of another.
   *)

Create HintDb subterm_relation discriminated.
Create HintDb rec_decision discriminated.

(** This is used to simplify the proof-search for recursive call obligations. *)

Ltac simpl_let :=
  match goal with
    [ H : let _ := ?t in _ |- _ ] =>
    match t with
    | fixproto => fail 1
    | _ => cbv zeta in H
    end
  end.

#[export] Hint Extern 40 => progress (cbv beta in * || simpl_let) : rec_decision.

(* This expands lets in the context to simplify proof search for recursive call
  obligations, as [eauto] does not do matching up-to unfolding of let-bound variables.
*)

#[export] Hint Extern 10 => 
  match goal with
  [ x := _ |- _ ] => 
    lazymatch goal with
    |- context [ x ] => subst x 
    end
  end : rec_decision.

(** We can automatically use the well-foundedness of a relation to get
   the well-foundedness of its transitive closure.
   Note that this definition is transparent as well as [wf_clos_trans],
   to allow computations with functions defined by well-founded recursion.
   *)

Lemma WellFounded_trans_clos `(WF : WellFounded A R) : WellFounded (trans_clos R).
Proof. apply wf_trans_clos. apply WF. Defined.

#[export] Hint Extern 4 (WellFounded (trans_clos _)) =>
  apply @WellFounded_trans_clos : typeclass_instances.

#[export]
Instance wf_inverse_image {A R} `(WellFounded A R) {B} (f : B -> A) : WellFounded (inverse_image R f).
Proof. red. apply wf_inverse_image. apply H. Defined.

(* (* Do not apply [wf_MR] agressively, as Coq's unification could "invent" an [f] otherwise *)
(*    to unify. *) *)

(* #[export] Hint Extern 0 (WellFounded (inverse_image _ _)) => apply @wf_inverse_image : typeclass_instances. *)

#[export] Hint Extern 0 (inverse_image _ _ _ _) => red : rec_decision.

(** We also add hints for transitive closure, not using [t_trans] but forcing to 
   build the proof by successive applications of the inner relation. *)

#[export] Hint Resolve t_step : subterm_relation.

Lemma trans_clos_stepr A (R : Relation A) (x y z : A) :
  R y z -> trans_clos R x y -> trans_clos R x z.
Proof. intros Hyz Hxy. exact (t_trans _ x y z Hxy (t_step _ _ _ Hyz)). Defined.

#[export] Hint Resolve trans_clos_stepr : subterm_relation.

(** The default tactic to build proofs of well foundedness of subterm relations. *)

Create HintDb solve_subterm discriminated.

#[export] Hint Extern 4 (_ = _) => reflexivity : solve_subterm.
#[export] Hint Extern 10 => eapply_hyp : solve_subterm.

Ltac solve_subterm := intros;
  apply WellFounded_trans_clos;
  red; intros; simp_sigmas; on_last_hyp ltac:(fun H => depind H); constructor;
  intros; simp_sigmas; on_last_hyp ltac:(fun HR => depind HR);
  simplify_dep_elim; try typeclasses eauto with solve_subterm.

(** A tactic to launch a well-founded recursion. *)

Ltac rec_wf_fix recname kont :=
  let hyps := fresh in intros hyps;
  intro; on_last_hyp ltac:(fun x => rename x into recname;
                           unfold inverse_image at 1 in recname) ;
  destruct_right_sigma hyps; try curry recname; simpl in recname;
  kont recname.

(* Ltac rec_wf_fix x recname fixterm := *)
(*   apply fixterm ; clear_local ;  *)
(*   intros until 1 ; simp_sigmas ;  *)
(*     on_last_hyp ltac:(fun x => rename x into recname) ; *)
(*   simplify_dep_elim ; intros ; unblock_goal ; intros ; *)
(*   move recname at bottom ; try curry recname ; simpl in recname. *)

(** The [do] tactic but using a Coq-side nat. *)

Local Open Scope nat_scope.

Ltac do_nat n tac :=
  match n with
    | 0 => idtac
    | S ?n' => tac ; do_nat n' tac
  end.

(** Generalize an object [x], packing it in a sigma type if necessary. *)

Ltac sigma_pack n t :=
  let packhyps := fresh "hypspack" in
  let xpack := fresh "pack" in
  let eos' := fresh "eos" in
  match constr:(n) with
  | 0%nat => set (eos' := the_end_of_the_section); move eos' at top
  | _ => do_nat n ltac:(idtac; revert_last); set (eos' := the_end_of_the_section);
         do_nat n intro
  end;
  uncurry_hyps packhyps;
  (progress (set(xpack := t) in |- ;
             cbv beta iota zeta in xpack; revert xpack;
             pattern sigma packhyps;
             clearbody packhyps;
             revert packhyps;
             clear_nonsection; clear eos')).

(** We specialize the tactic for [x] of type [A], first packing 
   [x] with its indices into a sigma type and finding the declared 
   relation on this type. *)

Ltac rec_wf recname t kont := 
  sigma_pack 0 t;
    match goal with
      [ |- forall (s : ?T) (s0 := @?b s), @?P s ] => 
      let fn := constr:(fun s : T => b s) in
      let c := constr:(wellfounded (R:=inverse_image _ fn)) in
      let wf := constr:(FixWf (WF:=c)) in
      intros s _; revert s; refine (wf P _); simpl ;
      rec_wf_fix recname kont
    end. 

Ltac rec_wf_eqns recname x := 
  rec_wf recname x 
         ltac:(fun rechyp => add_pattern (hide_pattern rechyp)).

Ltac rec_wf_rel_aux recname n t rel kont :=
  sigma_pack n t;
    match goal with
      [ |- forall (s : ?T) (s0 := @?b s), @?P s ] => 
      let fn := constr:(fun s : T => b s) in
      let c := constr:(wellfounded (R:=inverse_image rel fn)) in
      let wf := constr:(FixWf (WF:=c)) in
      intros s _; revert s; refine (wf P _); simpl ;
      rec_wf_fix recname kont
    end.

Ltac rec_wf_rel recname x rel :=
  rec_wf_rel_aux recname 0 x rel ltac:(fun rechyp => idtac).

(* NoCycle from well-foundedness. *)

Definition NoCycle_WellFounded {A} (R : Relation A) (wfR : WellFounded R) : NoCyclePackage A :=
  {| NoCycle := R;
     noCycle := well_founded_irreflexive (wfR:=wfR) |}.
#[export] Existing Instance NoCycle_WellFounded.

#[export] Hint Extern 30 (@NoCycle ?A (NoCycle_WellFounded ?R ?wfr) _ _) =>
  hnf; typeclasses eauto with subterm_relation : typeclass_instances.
