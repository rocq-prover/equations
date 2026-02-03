(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Tactics related to (dependent) equality and proof irrelevance. *)

From Stdlib Require Import Program.Tactics.
Require Export Equations.Init.
From Equations Require Import CoreTactics.
From Equations Require Import Signature.
From Equations.Prop Require Import Logic.
From Equations.Prop Require Import Classes.
From Equations.Prop Require Import EqDec.

Import Sigma_Notations.
Local Open Scope equations_scope.

Local Set Keyed Unification.

Unset Universe Polymorphism.

(** Support for the [Equations] command.
   These tactics implement the necessary machinery to solve goals produced by the
   [Equations] command relative to dependent pattern-matching.
   It is inspired from the "Eliminating Dependent Pattern-Matching" paper by
   Goguen, McBride and McKinna. *)

(** The [DependentEliminationPackage] provides the default dependent elimination principle to
   be used by the [equations] resolver. It is especially useful to register the dependent elimination
   principles for things in [Prop] which are not automatically generated. *)

Polymorphic
Class DependentEliminationPackage (A : Type) :=
  { elim_type : Type ; elim : elim_type }.

(** A higher-order tactic to apply a registered eliminator. *)

Ltac elim_tac tac p :=
  let ty := type of p in
  let eliminator := eval simpl in (elim (A:=ty)) in
    tac p eliminator.

(** Specialization to do case analysis or induction.
   Note: the [equations] tactic tries [case] before [elim_case]: there is no need to register
   generated induction principles. *)

Ltac elim_case p := elim_tac ltac:(fun p el => destruct p using el) p.
Ltac elim_ind p := elim_tac ltac:(fun p el => induction p using el) p.

(** Lemmas used by the simplifier, mainly rephrasings of [eq_rect], [eq_ind]. *)

Notation "p # t" := (transport _ p t) (right associativity, at level 65) : equations_scope.

Definition solution_left {A} {B : A -> Type} (t : A) (p : B t) (x : A) (e : x = t) : B x :=
  eq_sym e # p.

Lemma eq_sym_invol {A} (x y : A) (e : x = y) : eq_sym (eq_sym e) = e.
Proof. destruct e. reflexivity. Defined.

Lemma eq_symmetry_dep {A} {t : A} {B : forall (x : A), x = t -> Type} :
  (forall (x : A) (eq : t = x), B x (eq_sym eq)) ->
  (forall (x : A) (eq : x = t), B x eq).
Proof.
  intros. rewrite <- eq_sym_invol.
  generalize (eq_sym eq). apply X.
Defined.

Lemma solution_left_dep : forall {A} (t : A) {B : forall (x : A), (x = t -> Type)},
    B t eq_refl -> (forall x (Heq : x = t), B x Heq).
Proof.
  intros A t B H x eq. apply eq_symmetry_dep. clear eq. intros.
  destruct eq. exact H.
Defined.

Definition solution_right {A} {P : A -> Type} (t : A) (p : P t) x (e : t = x) : P x :=
  transport P e p.

Lemma solution_right_dep : forall {A} (t : A) {B : forall (x : A), (t = x -> Type)},
    B t eq_refl -> (forall x (Heq : t = x), B x Heq).
Proof. intros A t B H x eq. destruct eq. apply H. Defined.

Lemma solution_left_let : forall {A} {B : A -> Type} (b : A) (t : A),
  (b = t -> B t) -> (let x := b in x = t -> B x).
Proof. intros A B b t H x eq. subst x. destruct eq. apply H. reflexivity. Defined.

Lemma solution_right_let : forall {A} {B : A -> Type} (b t : A),
  (t = b -> B t) -> (let x := b in t = x -> B x).
Proof. intros A B b t H x eq. subst x. destruct eq. apply H. reflexivity. Defined.

Lemma deletion : forall {A B} (t : A), B -> (t = t -> B).
Proof. intros; assumption. Defined.

(** Old-style sigma types. *)
Lemma simplification_existT1 : forall {A} {P : A -> Type} {B} (p q : A) (x : P p) (y : P q),
  (p = q -> existT P p x = existT P q y -> B) -> (existT P p x = existT P q y -> B).
Proof.
  intros. refine (X _ H).
  change (projT1 (existT P p x) = projT1 (existT P q y)).
  now destruct H.
Defined.

Polymorphic Lemma simplification_sigma1@{i j | i <= eq.u0} :
  forall {A : Type@{i}} {P : A -> Type@{i}} {B : Type@{j}}
         (p q : A) (x : P p) (y : P q),
  (p = q -> (p, x) = (q, y) -> B) -> ((p, x) = (q, y) -> B).
Proof.
  intros. refine (X _ H).
  change (pr1 (p, x) = pr1 (q, y)).
  now destruct H.
Defined.

Polymorphic Lemma eq_simplification_sigma1@{i j | i <= eq.u0} {A : Type@{i}} {P : Type@{i}} {B : Type@{j}}
  (p q : A) (x : P) (y : P) :
  (p = q -> x = y -> B) ->
  ((p, x) = (q, y) -> B).
Proof.
  intros. revert X.
  change p with (pr1 (p, x)).
  change q with (pr1 (q, y)).
  change x with (pr2 (p, x)) at 2.
  change y with (pr2 (q, y)) at 2.
  destruct H.
  intros X. eapply (X eq_refl). apply eq_refl.
Defined.

Polymorphic Lemma eq_simplification_sigma1_dep@{i j | i <= eq.u0 +} {A : Type@{i}} {P : A -> Type@{i}} {B : Type@{j}}
  (p q : A) (x : P p) (y : P q) :
  (forall e : p = q, (@eq_rect A p P x q e) = y -> B) ->
  ((p, x) = (q, y) -> B).
Proof.
  intros. revert X.
  change p with (pr1 (p, x)).
  change q with (pr1 (q, y)).
  change x with (pr2 (p, x)) at 3.
  change y with (pr2 (q, y)) at 4.
  destruct H.
  intros X. eapply (X eq_refl). apply eq_refl.
Defined.

Polymorphic Definition pack_sigma_eq_nondep@{i | i <= eq.u0} {A : Type@{i}} {P : Type@{i}} {p q : A} {x : P} {y : P}
  (e' : p = q) (e : x = y) : (p, x) = (q, y).
Proof. destruct e'. simpl in e. destruct e. apply eq_refl. Defined.

Polymorphic Lemma eq_simplification_sigma1_nondep_dep@{i j | i <= eq.u0} {A : Type@{i}} {P : Type@{i}}
  (p q : A) (x : P) (y : P) {B : (p, x) = (q, y) -> Type@{j}} :
  (forall e' : p = q, forall e : x = y, B (pack_sigma_eq_nondep e' e)) ->
  (forall e : sigmaI (fun _ => P) p x = sigmaI (fun _ => P) q y, B e).
Proof.
  intros. revert X.
  change p with (pr1 (p, x)).
  change q with (pr1 (q, y)).
  change x with (pr2 (p, x)) at 2 4.
  change y with (pr2 (q, y)) at 2 4.
  destruct e.
  intros X. simpl in *.
  apply (X eq_refl eq_refl).
Defined.

Polymorphic Definition pack_sigma_eq@{i | +} {A : Type@{i}} {P : A -> Type@{i}} {p q : A} {x : P p} {y : P q}
  (e' : p = q) (e : @eq_rect A p P x q e' = y) : (p, x) = (q, y).
Proof. destruct e'. simpl in e. destruct e. apply eq_refl. Defined.

Polymorphic Lemma eq_simplification_sigma1_dep_dep@{i j | i <= eq.u0 +} {A : Type@{i}} {P : A -> Type@{i}}
  (p q : A) (x : P p) (y : P q) {B : (p, x) = (q, y) -> Type@{j}} :
  (forall e' : p = q, forall e : @eq_rect A p P x q e' = y, B (pack_sigma_eq e' e)) ->
  (forall e : (p, x) = (q, y), B e).
Proof.
  intros. revert X.
  change p with (pr1 (p, x)).
  change q with (pr1 (q, y)).
  change x with (pr2 (p, x)) at 3 5.
  change y with (pr2 (q, y)) at 4 6.
  destruct e.
  intros X. simpl in *.
  apply (X eq_refl eq_refl).
Defined.
Set Printing Universes.
Polymorphic Lemma pr2_inv_uip@{i| i <= eq.u0 +} {A : Type@{i}}
            {P : A -> Type@{i}} {x : A} {y y' : P x} :
  y = y' -> sigmaI@{i} P x y = sigmaI@{i} P x y'.
Proof. exact (solution_right (P:=fun y' => (x, y) = (x, y')) y eq_refl y'). Defined.

Polymorphic Lemma pr2_uip@{i | +} {A : Type@{i}}
            {E : UIP A} {P : A -> Type@{i}} {x : A} {y y' : P x} :
  sigmaI@{i} P x y = sigmaI@{i} P x y' -> y = y'.
Proof.
  refine (eq_simplification_sigma1_dep_dep@{i i} _ _ _ _ _).
  intros e'. destruct (uip eq_refl e'). intros e ; exact e.
Defined.

Polymorphic Lemma pr2_uip_refl@{i | +} {A : Type@{i}}
            {E : UIP A} (P : A -> Type@{i}) (x : A) (y : P x) :
  pr2_uip@{i} (@eq_refl _ (x, y)) = eq_refl.
Proof.
  unfold pr2_uip, eq_simplification_sigma1_dep_dep.
  now rewrite uip_refl_refl.
Defined.

(** If we have decidable equality on [A] we use this version which is 
   axiom-free! *)

Polymorphic Lemma simplification_sigma2_uip@{i j |+} :
  forall {A : Type@{i}} `{UIP A} {P : A -> Type@{i}} {B : Type@{j}}
    (p : A) (x y : P p),
    (x = y -> B) -> ((p , x) = (p, y) -> B).
Proof. intros. apply X. apply pr2_uip@{i} in H0. assumption. Defined.

Polymorphic Lemma simplification_sigma2_uip_refl@{i j | +} :
  forall {A : Type@{i}} {uip:UIP A} {P : A -> Type@{i}} {B : Type@{j}}
    (p : A) (x : P p) (G : x = x -> B),
      @simplification_sigma2_uip A uip P B p x x G eq_refl = G eq_refl.
Proof.
  intros. unfold simplification_sigma2_uip. now rewrite pr2_uip_refl.
Defined.

Arguments simplification_sigma2_uip : simpl never.

Polymorphic Lemma simplification_sigma2_dec_point :
  forall {A : Type} (p : A) `{EqDecPoint A p} {P : A -> Type} {B : Type}
    (x y : P p),
    (x = y -> B) -> ((p, x) = (p, y) -> B).
Proof. intros. apply X. apply inj_right_sigma_point in H0. assumption. Defined.

Polymorphic Lemma simplification_sigma2_dec_point_refl@{i +} :
  forall {A} (p : A) `{eqdec:EqDecPoint A p} {P : A -> Type} {B}
    (x : P p) (G : x = x -> B),
      @simplification_sigma2_dec_point A p eqdec P B x x G eq_refl = G eq_refl.
Proof.
  intros. unfold simplification_sigma2_dec_point.
  rewrite inj_right_sigma_refl_point. reflexivity.
Defined.
Arguments simplification_sigma2_dec_point : simpl never.

Polymorphic Lemma simplification_K_uip@{i j| i <= eq.u0 +} {A : Type@{i}} `{UIP A} (x : A) {B : x = x -> Type@{j}} :
  B eq_refl -> (forall p : x = x, B p).
Proof. apply UIP_K. Defined.
Arguments simplification_K_uip : simpl never.

Polymorphic Lemma simplification_K_uip_refl :
  forall {A} `{UIP A} (x : A) {B : x = x -> Type} (p : B eq_refl),
  simplification_K_uip x p eq_refl = p.
Proof.
  intros.
  unfold simplification_K_uip, UIP_K. now rewrite uip_refl_refl.
Defined.

Polymorphic
Definition ind_pack_eq@{i | +} {A : Type@{i}} {B : A -> Type@{i}} {x : A} {p q : B x} (e : p = q) :
  @eq (sigma (fun x => B x)) (x, p) (x, q) :=
  (pr2_inv_uip e).

Polymorphic
Definition ind_pack_eq_inv_equiv@{i} {A : Type@{i}} {uip : UIP A}
           {B : A -> Type@{i}} {x : A} (p q : B x) (e : p = q) :
  pr2_uip (pr2_inv_uip e) = e.
Proof.
  destruct e. apply pr2_uip_refl.
Defined.

Polymorphic
Definition opaque_ind_pack_eq_inv@{i j} {A : Type@{i}} {uip : UIP A}
  {B : A -> Type@{i}} {x : A} {p q : B x} (G : p = q -> Type@{j}) (e : (x, p) = (x, q)) :=
  G (pr2_uip@{i} e).
Arguments opaque_ind_pack_eq_inv : simpl never.
Arguments pr2_uip : simpl never.
Arguments pr2_inv_uip : simpl never.

Polymorphic
Lemma simplify_ind_pack@{i j | +} {A : Type@{i}} {uip : UIP A}
      (B : A -> Type@{i}) (x : A) (p q : B x) (G : p = q -> Type@{j}) :
      (forall e : (x, p) = (x, q), opaque_ind_pack_eq_inv G e) ->
  (forall e : p = q, G e).
Proof.
  intros H. intros e. 
  specialize (H (ind_pack_eq e)). unfold opaque_ind_pack_eq_inv in H.
  rewrite ind_pack_eq_inv_equiv in H. apply H.
Defined.
Arguments simplify_ind_pack : simpl never.

Polymorphic
Lemma simplify_ind_pack_inv@{i j | +} {A : Type@{i}} {uip : UIP A}
      (B : A -> Type@{i}) (x : A) (p : B x) (G : p = p -> Type@{j}) :
  G eq_refl -> opaque_ind_pack_eq_inv G eq_refl.
Proof.
  intros H. unfold opaque_ind_pack_eq_inv. destruct (pr2_uip_refl B x p). exact H.
Defined.
Arguments simplify_ind_pack_inv : simpl never.

Polymorphic
Definition simplified_ind_pack@{i j | +} {A : Type@{i}} {uip : UIP A}
  (B : A -> Type@{i}) (x : A) (p : B x) (G : p = p -> Type@{j})
  (t : opaque_ind_pack_eq_inv G eq_refl) :=
  eq_rect _ G t _ (@pr2_uip_refl A uip B x p).
Arguments simplified_ind_pack : simpl never.

Polymorphic
Lemma simplify_ind_pack_refl@{i j | +} {A : Type@{i}} {uip : UIP A}
(B : A -> Type@{i}) (x : A) (p : B x) (G : p = p -> Type@{j})
(t : forall (e : (x, p) = (x, p)), opaque_ind_pack_eq_inv G e) :
  simplify_ind_pack B x p p G t eq_refl =
  simplified_ind_pack B x p G (t eq_refl).
Proof. reflexivity. Qed.

Polymorphic
Lemma simplify_ind_pack_elim@{i j | +} {A : Type@{i}} {uip : UIP A}
  (B : A -> Type@{i}) (x : A) (p : B x) (G : p = p -> Type@{j})
  (t : G eq_refl) :
  simplified_ind_pack B x p G (simplify_ind_pack_inv B x p G t) = t.
Proof.
  unfold simplified_ind_pack, simplify_ind_pack_inv.
  now destruct (pr2_uip_refl B x p).
Qed.

(** All the simplification rules involving axioms are treated as opaque 
  when proving lemmas about definitions. To actually compute with these
  inside Coq, one has to make them transparent again. *)

Global Opaque simplification_sigma2_uip
       simplification_sigma2_dec_point
       simplification_K_uip
       simplify_ind_pack simplified_ind_pack.
Global Opaque opaque_ind_pack_eq_inv.

Ltac rewrite_sigma2_refl_noK :=
  match goal with
  | |- context [@inj_right_sigma ?A ?H ?x ?P ?y ?y' _] =>
    rewrite (@inj_right_sigma_refl A H x P y)

  | |- context [@simplification_sigma2_uip ?A ?H ?P ?B ?p ?x ?y ?X eq_refl] =>
    rewrite (@simplification_sigma2_uip_refl A H P B p x X); simpl

  | |- context [@simplification_sigma2_dec_point ?A ?p ?H ?P ?B ?x ?y ?X eq_refl] =>
    rewrite (@simplification_sigma2_dec_point_refl A p H P B x X); simpl

  | |- context [@simplification_K_uip ?A ?dec ?x ?B ?p eq_refl] =>
    rewrite (@simplification_K_uip_refl A dec x B p); simpl eq_rect

  (* | |- context [@HSets.inj_sigma_r ?A ?H ?P ?x ?y ?y' _] => *)
  (*   rewrite (@HSets.inj_sigma_r_refl A H P x y) *)

  | |- context [@simplify_ind_pack ?A ?uip ?B ?x ?p _ ?G _ eq_refl] =>
    rewrite (@simplify_ind_pack_refl A uip B x p G _)

  | |- context [@simplified_ind_pack ?A ?uip ?B ?x ?p ?G
        (simplify_ind_pack_inv _ _ _ _ ?t)] =>
    rewrite (@simplify_ind_pack_elim A uip B x p G t)
  end.

Ltac rewrite_sigma2_refl := rewrite_sigma2_refl_noK.

(** This hint database and the following tactic can be used with [autounfold] to 
   unfold everything to [eq_rect]s. *)

Create HintDb equations.

#[global]
Hint Unfold solution_left solution_right
  eq_sym_invol eq_symmetry_dep
  solution_left_dep solution_right_dep deletion
  simplification_existT1 simplification_sigma1
  eq_simplification_sigma1 eq_simplification_sigma1_dep
  apply_noConfusion
  eq_rect_r eq_rec eq_ind eq_ind_r
  : equations.

(** Makes these definitions disappear at extraction time *)
Extraction Inline solution_right_dep solution_right solution_left solution_left_dep.
Extraction Inline eq_sym_invol eq_symmetry_dep.
Extraction Inline solution_right_let solution_left_let deletion.
Extraction Inline simplification_existT1.
Extraction Inline simplification_sigma1 simplification_sigma2_uip.
Extraction Inline simplification_K_uip.
Extraction Inline eq_simplification_sigma1 eq_simplification_sigma1_dep.
Extraction Inline eq_simplification_sigma1_nondep_dep eq_simplification_sigma1_dep_dep.

(** Simply unfold as much as possible. *)

Ltac unfold_equations := repeat progress autounfold with equations.
Ltac unfold_equations_in H := repeat progress autounfold with equations in H.

Ltac rewrite_refl_id :=
  repeat (progress (autorewrite with refl_id) || (try rewrite_sigma2_refl)).

Ltac simplify_equations_in e :=
  repeat progress (autounfold with equations in e ; simpl in e).

(** Using these we can make a simplifier that will perform the unification
   steps needed to put the goal in normalised form (provided there are only
   constructor forms). Compare with the lemma 16 of the paper.
   We don't have a [noCycle] procedure yet. *)

(** These two tactics are dangerous as they can try to reduce terms
    to head-normal-form and take ages to fail. *)
Ltac try_discriminate := discriminate.
Ltac try_injection H := injection H.

Ltac simplify_one_dep_elim :=
  match goal with
    | [ |- context [eq_rect_r _ _ eq_refl]] => progress simpl eq_rect_r
    | [ |- context [eq_rect _ _ _ _ eq_refl]] => progress simpl eq_rect
    | [ |- context [transport _ eq_refl _]] => progress simpl transport
    | [ |- context [@eq_elim _ _ _ _ _ eq_refl]] => progress simpl eq_rect
    | [ |- context [@eq_elim_r _ _ _ _ _ eq_refl]] => progress simpl eq_elim_r
    | [ |- context [noConfusion_inv _]] => progress simpl noConfusion_inv
    | [ |- @opaque_ind_pack_eq_inv ?A ?uip ?B ?x ?p _ ?G eq_refl] =>
            apply (@simplify_ind_pack_inv A uip B x p G)
    | [ |- let _ := block in _ ] => fail 1
    | [ |- _ ] => (simplify * || simplify ?); cbv beta
    | [ |- _ -> ?B ] => let ty := type of B in (* Works only with non-dependent products *)
      intro || (let H := fresh in intro H)
    | [ |- forall x, _ ] => let H := fresh x in intro H
    | [ |- _ ] => intro
  end.

(** Repeat until no progress is possible. By construction, it should leave the goal with
   no remaining equalities generated by the [generalize_eqs] tactic. *)

Ltac simplify_dep_elim := repeat simplify_one_dep_elim.

(** Apply [noConfusion] on a given hypothsis. *)

Ltac noconf H :=
  block_goal; revert_until H; block_goal;
  on_last_hyp ltac:(fun H' => revert H');
  simplify_dep_elim;
  intros_until_block;
  intros_until_block.

(** Reverse and simplify. *)

Ltac simpdep := reverse; simplify_dep_elim.

(** Decompose existential packages. *)

Ltac decompose_exists id id' := hnf in id ;
  match type of id with
    | @sigma _ _ => let xn := fresh id "'" in
      destruct id as [xn id]; decompose_exists xn id;
        cbv beta delta [ pr1 pr2 ] iota in id, id';
          decompose_exists id id'
    | _ => cbv beta delta [ pr1 pr2 ] iota in id, id'
  end.

(** Dependent generalization using existentials only. *)

Ltac generalize_sig_gen id cont :=
  let id' := fresh id in
  get_signature_pack id id';
  hnf in (value of id'); hnf in (type of id');
  lazymatch goal with
  | id' := ?v |- context[ id ] =>
    generalize (@eq_refl _ id' : v = id') ;
    clearbody id'; simpl in id';
    cont id id' id v
  | id' := ?v |- _ =>
    let id'1 := fresh id' in let id'2 := fresh id' in
    set (id'2 := pr2 id'); set (id'1 := pr1 id') in id'2;
    hnf in (value of id'1), (value of id'2);
    try red in (type of id'2);
    match goal with
      [ id'1 := ?t |- _ ] =>
      generalize (@eq_refl _ id'1 : t = id'1);
        clearbody id'2 id'1; clear id' id;
        try unfold signature in id'2; hnf in id'2; simpl in id'2;
        rename id'2 into id; cont id id id'1 t
    end
  end.

Ltac generalize_sig id cont :=
  generalize_sig_gen id
    ltac:(fun id id' id'1 t => (* Fails if id = id' *)
            try rename id into id', id' into id;
          cont id'1 id).

Ltac generalize_sig_vars id cont :=
  generalize_sig_gen id
    ltac:(fun id id' id'1 t => move_after_deps id' t; revert_until id';
          rename id' into id; cont id'1 id).

Ltac generalize_sig_dest id :=
  generalize_sig id ltac:(fun id id' => decompose_exists id id').

Ltac generalize_sig_vars_dest id :=
  generalize_sig_vars id ltac:(fun id id' => decompose_exists id id').

Ltac generalize_eqs_sig id :=
  (needs_generalization id ; generalize_sig_dest id)
    || idtac.

Ltac generalize_eqs_vars_sig id :=
  (needs_generalization id ; generalize_sig_vars_dest id)
    || idtac.

(** The default implementation of generalization using sigma types. *)

Ltac generalize_by_eqs id := generalize_eqs_sig id.
Ltac generalize_by_eqs_vars id := generalize_eqs_vars_sig id.

(** Do dependent elimination of the last hypothesis, but not simplifying yet
   (used internally). *)

Ltac destruct_last :=
  on_last_hyp ltac:(fun id => simpl in id ; generalize_by_eqs id ; destruct id).

(** The rest is support tactics for the [Equations] command. *)

(** To solve a goal by inversion on a particular target. *)

Ltac do_empty id :=
  exfalso ; simpl in id ;
  solve [ generalize_by_eqs id ; destruct id ; simplify_dep_elim
    | apply id ; eauto with simp ].

(** If defining recursive functions, the prototypes come first. *)

Ltac introduce p := first [
  match p with _ => (* Already there, generalize dependent hyps *)
    generalize dependent p ; intros p
  end
  | intros until p | intros until 1 | intros ].

Ltac do_case p := introduce p ; (elim_case p || destruct p || (case p ; clear p)).
Ltac do_ind p := introduce p ; (elim_ind p || induction p).

(** The following tactics allow to do induction on an already instantiated inductive predicate
   by first generalizing it and adding the proper equalities to the context, in a maner similar to
   the BasicElim tactic of "Elimination with a motive" by Conor McBride. *)

(** The [do_depelim] higher-order tactic takes an elimination tactic as argument and an hypothesis 
   and starts a dependent elimination using this tactic. *)

Ltac is_introduced H :=
  match goal with
    | [ H' : _ |- _ ] => match H' with H => idtac end
  end.

Tactic Notation "intro_block" hyp(H) :=
  (is_introduced H ; block_goal ; revert_until H ; block_goal) ||
    (let H' := fresh H in intros until H' ; block_goal) || (intros ; block_goal).

Tactic Notation "intro_block_id" ident(H) :=
  (is_introduced H ; block_goal ; revert_until H ; block_goal) ||
    (let H' := fresh H in intros until H' ; block_goal) || (intros ; block_goal).

Ltac unblock_dep_elim :=
  match goal with
    | |- let _ := block in ?T => 
      match T with context [ block ] => 
        change T ; intros_until_block
      end
    | _ => unblock_goal
  end.


(** A tactic that tries to remove trivial equality guards in induction hypotheses coming
   from [dependent induction]/[generalize_eqs] invocations. *)

Ltac simplify_IH_hyps := repeat
  match goal with
    | [ hyp : context [ block ] |- _ ] => 
     cbn beta in hyp; eqns_specialize_eqs_block hyp; 
    cbn beta iota delta[eq_rect_r eq_rect] zeta in hyp
  end.

Ltac simpl_dep_elim := simplify_dep_elim ; simplify_IH_hyps ; unblock_dep_elim.

Ltac do_intros H :=
  (try intros until H) ; (intro_block_id H || intro_block H) ;
  (try simpl in H ; simplify_equations_in H).

Ltac do_depelim_nosimpl tac H := do_intros H ; generalize_by_eqs H ; tac H.

Ltac do_depelim tac H := do_depelim_nosimpl tac H ; simpl_dep_elim; unblock_goal.

Ltac do_depind tac H := 
  (try intros until H) ; intro_block H ; (try simpl in H ; simplify_equations_in H) ;
  generalize_by_eqs_vars H ; 
  block_goal ;
  tac H ; 
  intros_until_block; 
  simpl_dep_elim; unblock_goal.

(** To dependent elimination on some hyp. *)

Ltac depelim id := do_depelim ltac:(fun hyp => do_case hyp) id.

Ltac depelim_term c :=
  let H := fresh "term" in
    set (H:=c) in *; clearbody H ; depelim H.

(** Used internally. *)

Ltac depelim_nosimpl id := do_depelim_nosimpl ltac:(fun hyp => do_case hyp) id.

(** To dependent induction on some hyp. *)

Ltac depind id := do_depind ltac:(fun hyp => do_ind hyp) id.

(** A variant where generalized variables should be given by the user. *)

Ltac do_depelim' tac H :=
  (try intros until H) ; block_goal ; generalize_by_eqs H ; tac H ; simplify_dep_elim ; 
    simplify_IH_hyps ; unblock_goal.

(** Calls [destruct] on the generalized hypothesis, results should be similar to inversion.
   By default, we don't try to generalize the hyp by its variable indices.  *)

Tactic Notation "dependent" "destruction" ident(H) := 
  do_depelim' ltac:(fun hyp => do_case hyp) H.

Tactic Notation "dependent" "destruction" ident(H) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => destruct hyp using c) H.

(** This tactic also generalizes the goal by the given variables before the elimination. *)

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depelim' ltac:(fun hyp => revert l ; do_case hyp) H.

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => revert l ; destruct hyp using c) H.

(** Then we have wrappers for usual calls to induction. One can customize the induction tactic by 
   writting another wrapper calling do_depelim. We suppose the hyp has to be generalized before
   calling [induction]. *)

Tactic Notation "dependent" "induction" ident(H) :=
  do_depind ltac:(fun hyp => do_ind hyp) H.

Tactic Notation "dependent" "induction" ident(H) "using" constr(c) :=
  do_depind ltac:(fun hyp => induction hyp using c) H.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depelim' ltac:(fun hyp => generalize l ; clear l ; do_ind hyp) H.

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => generalize l ; clear l ; induction hyp using c) H.

(** [solve_equation] is used to prove the equation lemmas for an existing definition.  *)

Ltac find_empty := simpl in * ; exfalso ;
  match goal with
    | [ H : _ |- _ ] => solve [ clear_except H ; dependent elimination H | eqns_specialize_eqs H ; assumption ]
    | [ H : _ <> _ |- _ ] => solve [ red in H ; eqns_specialize_eqs H ; assumption ]
  end.

Ltac make_simplify_goal :=
  match goal with 
    [ |- @eq ?A ?T ?U ] => let eqP := fresh "eqP" in 
      set (eqP := fun x : A => x = U) ; change (eqP T)
  end.

Ltac hnf_gl :=
  match goal with 
    [ |- ?P ?T ] => let T' := eval hnf in T in
      change_no_check (P T')
  end.

Ltac hnf_eq :=
  match goal with
    |- ?x = ?y =>
      let x' := eval hnf in x in
      let y' := eval hnf in y in
      change_no_check (x' = y')
  end.

Ltac red_eq_lhs :=
  match goal with
    |- ?R ?x ?y =>
      let x' := eval red in x in
      change_no_check (R x' y)
  end.

Ltac red_one_eq :=
  match goal with
  |- ?R ?x ?y =>
    let x' := eval red in x in
    let y' := eval red in y in
    change_no_check (R x' y')
  end.
  
Ltac red_eq :=
  match goal with
    |- ?x = ?y =>
    let rec reduce_eq x y :=
      let x' := eval red in x in
      let y' := eval red in y in
          (reduce_eq x' y' || change_no_check (x' = y'))
      in reduce_eq x y
  end.

Ltac red_gl :=
  match goal with
    |- ?P ?x =>
    let rec reduce x :=
      let x' := eval red in x in
      (reduce x' || change_no_check (P x'))
      in reduce x
  end.

Ltac rewrite_sigma2_rule_noK c :=
  match c with
  | @inj_right_sigma ?A ?H ?x ?P ?y ?y' _ =>
    rewrite (@inj_right_sigma_refl A H x P y)
  | @simplify_ind_pack ?A ?uip ?B ?x ?p _ ?G _ eq_refl=>
    rewrite (@simplify_ind_pack_refl A uip B x p G _)
  | @simplification_sigma2_uip ?A ?H ?P ?B ?p ?x ?y ?X eq_refl=>
    rewrite (@simplification_sigma2_uip_refl A H P B p x X); simpl
  | @simplification_sigma2_dec_point ?A ?p ?H ?P ?B ?x ?y ?X eq_refl=>
    rewrite (@simplification_sigma2_dec_point_refl A p H P B x X); simpl
  | @simplification_K_uip ?A ?dec ?x ?B ?p eq_refl=>
    rewrite (@simplification_K_uip_refl A dec x B p); simpl eq_rect
  end.

Ltac rewrite_sigma2_rule c :=
  rewrite_sigma2_rule_noK c.

Ltac rewrite_sigma2_term x :=
  match x with
   | ?f _ _ _ _ _ _ _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ _ _ _ _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ _ _ _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ _ _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ _ => rewrite_sigma2_rule f
   | ?f _ _ => rewrite_sigma2_rule f
   | ?f _ => rewrite_sigma2_rule f
   | ?f => rewrite_sigma2_rule f
  end.

Ltac rewrite_sigma2_refl_eq :=
  match goal with
    |- ?x = ?y => rewrite_sigma2_term x || rewrite_sigma2_term y
  end.

Ltac rewrite_sigma2_refl_goal :=
  match goal with
  | |- ?P ?x => rewrite_sigma2_term x
  end.

(* Ltac simpl_equations :=  *)
(*   repeat (repeat (simpl; (hnf_eq || rewrite_sigma2_refl_eq || autorewrite with refl_id); simpl); *)
(*           try progress autounfold with equations). *)

(* Ltac simplify_equation c := *)
(*   make_simplify_goal ; simpl ; *)
(*   repeat (try autounfoldify c; *)
(*           try (red_gl || rewrite_sigma2_refl_goal || autorewrite with refl_id) ; simpl). *)

Ltac simpl_equations :=
  repeat (repeat (simpl; hnf_eq; rewrite_refl_id);
          try progress autounfold with equations).

Ltac simpl_equation_impl :=
  repeat (unfold_equations; rewrite_refl_id).

Ltac simplify_equation c :=
  make_simplify_goal; simpl;
  repeat (try autounfold_ref c;
          progress (simpl; unfold_equations) ||
          (progress (autorewrite with refl_id)) ||
          reflexivity ||
          (progress (rewrite_sigma2_refl))).

Ltac solve_equation c :=
  intros ; try simplify_equation c ; try
    (match goal with 
       | [ |- ImpossibleCall _ ] => find_empty
       | _ => try red; try (reflexivity || discriminates)
     end).

Definition depelim_module := tt.

Register depelim_module as equations.depelim.module.
