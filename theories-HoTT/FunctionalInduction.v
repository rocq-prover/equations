(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Warnings "-notation-overridden".
From Equations Require Import CoreTactics.
From Equations Require Import HoTT.Logic HoTT.Classes HoTT.EqDec HoTT.DepElim.
From HoTT Require Import Spaces.Nat.

Local Open Scope nat_scope.
Local Open Scope equations_scope.
Import Sigma_Notations.

(** The tactic [funind c Hc] applies functional induction on the application 
   [c] which must be of the form [f args] where [f] has a [FunctionalInduction]
   instance. [Hc] is the name given to the call, used to generate hypothesis names. *)

Ltac funind c Hcall := 
  match c with
    context C [ ?f ] =>
      let x := constr:(fun_ind_prf (f:=f)) in
        (let prf := eval simpl in x in
         let p := context C [ prf ] in
         let prf := fresh in
         let call := fresh in
           assert(prf:=p) ;
           (* Abstract the call *)
           set(call:=c) in *; generalize (@idpath _ call : call = c); clearbody call ; intro Hcall ;
           (* Now do dependent elimination and simplifications *)
           dependent induction prf ; simplify_IH_hyps ; 
           (* Use the simplifiers for the constant to get a nicer goal. *)
           try simpc f in * ; try on_last_hyp ltac:(fun id => simpc f in id ; noconf id))
        || fail 1 "Internal error in funind"
  end || fail "Maybe you didn't declare the functional induction principle for" c.

Ltac funind_call f H :=
  on_call f ltac:(fun call => funind call H).

Ltac make_refine n c :=
  match constr:(n) with
  | 0 => uconstr:(c)
  | S ?n => make_refine n uconstr:(c _)
  end.

Ltac constr_head c :=
  let rec aux c :=
      match c with
      | ?f _ => aux f
      | ?f => f
      end
  in aux c.

Ltac with_last_secvar_aux tac :=
  match goal with
   [ H : _ |- _ ] => is_secvar H; tac H
  end.

Ltac with_last_secvar tac orelse := 
  with_last_secvar_aux tac + (* No section variables *) orelse.

Ltac get_elim c :=
  match c with
  | context [?f] => constr:(fun_elim (f:=f))
  end.

Ltac clear_non_secvar := repeat
  match goal with
  | [ H : _ |- _ ] => tryif is_secvar H then fail else clear H
  end.

Ltac remember_let H :=
  lazymatch goal with
  | [ H := ?body : ?type |- _ ] => generalize (1%path : H = body)
  end.

Ltac unfold_packcall packcall :=
  lazymatch goal with
    |- ?R ?x ?y -> ?P =>
    let y' := eval unfold packcall in y in
        change (R x y' -> P)
  end.

Ltac simplify_IHs_call := repeat
  match goal with
  | [ hyp : context [ block ] |- _ ] =>
    cbn beta in hyp; eqns_specialize_eqs_block hyp 2;
    cbn beta iota delta[transport paths_rect paths_rec paths_ind] zeta in hyp
  end.

Ltac make_packcall packcall c :=
  match goal with
  | [ packcall : ?type |- _ ] => change (let _ := c in type) in (type of packcall)
  end.

Ltac funelim_sig_tac c Heq simp_IHs tac :=
  let elimc := get_elim c in
  let packcall := fresh "packcall" in
  let packcall_fn := fresh "packcall_fn" in
  let elimfn := match elimc with fun_elim (f:=?f) => constr:(f) end in
  let elimn := match elimc with fun_elim (n:=?n) => constr:(n) end in
  block_goal;
  uncurry_call elimfn c packcall packcall_fn;
  remember_let packcall_fn; unfold_packcall packcall;
  (refine (simplification_sigma1 _ _ _ _ _) ||
   refine (simplification_sigma1_nondep_dep _ _ _ _ _) ||
   refine (simplification_sigma1_dep _ _ _ _ _));
  let H := fresh "eqargs" in
  let Heqfresh := fresh "__Heq__" in
  intros H Heqfresh; revert Heqfresh; block_goal;
  revert H;
  subst packcall_fn; clearbody packcall;
  make_packcall packcall elimfn;
  with_last_secvar ltac:(fun eos => move packcall before eos)
                          ltac:(move packcall at top);
  revert_until packcall; block_goal;
  cbv zeta in packcall; revert packcall; curry;
  let elimt := make_refine elimn elimc in
  unshelve refine_ho elimt; intros;
  cbv beta; simplify_dep_elim; intros_until_block;
  simplify_dep_elim;
  cbn beta iota delta [transport paths_rec paths_rect paths_ind pack_sigma pack_sigma_nondep] in *;
  simp_IHs; intros _ Heqfresh;
  unblock_goal;
  try (rewrite <- Heqfresh);
  try (rename Heqfresh into Heq || (let Heqf := fresh Heq in rename Heq into Heqf; rename Heqfresh into Heq));
  tac c.
  
Ltac funelim_constr_as c h simp_IHs := funelim_sig_tac c h simp_IHs ltac:(fun _ => idtac).

Ltac get_first_elim c :=
  match c with
  | ?x ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m => get_elim (x a b c d e f g h i j k l m)
  | ?x ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l => get_elim (x a b c d e f g h i j k l)
  | ?x ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k => get_elim (x a b c d e f g h i j k)
  | ?x ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j => get_elim (x a b c d e f g h i j)
  | ?x ?a ?b ?c ?d ?e ?f ?g ?h ?i => get_elim (x a b c d e f g h i)
  | ?x ?a ?b ?c ?d ?e ?f ?g ?h => get_elim (x a b c d e f g h)
  | ?x ?a ?b ?c ?d ?e ?f ?g => get_elim (x a b c d e f g)
  | ?x ?a ?b ?c ?d ?e ?f => get_elim (x a b c d e f)
  | ?x ?a ?b ?c ?d ?e => get_elim (x a b c d e)
  | ?x ?a ?b ?c ?d => get_elim (x a b c d)
  | ?x ?a ?b ?c => get_elim (x a b c)
  | ?x ?a ?b => get_elim (x a b)
  | ?x ?a => get_elim (x a)
  end.

(** An alternative tactic that does not generalize over the arguments.
    BEWARE: It might render the goal unprovable. *)

Ltac apply_funelim c :=
  let elimc := get_first_elim c in
  let elimfn := match elimc with fun_elim (f:=?f) => constr:(f) end in
  let elimn := match elimc with fun_elim (n:=?n) => constr:(n) end in
  let elimt := make_refine elimn elimc in
  apply_args c elimt ltac:(fun elimc => unshelve refine_ho elimc; cbv beta).

(** A special purpose database used to prove the elimination principle. *)

Create HintDb funelim.

(** Solve reflexivity goals. *)

#[export] Hint Extern 0 (_ = _) => constructor : funelim.

(** Specialize hypotheses begining with equalities. *)

Ltac specialize_hyps :=
  match goal with
  | [ H : forall _ : paths ?x ?x, _ |- _ ] =>
    specialize (H 1%path); unfold paths_rect, paths_rec, transport, paths_ind in H ; simpl in H
  end.

#[export] Hint Extern 100 => specialize_hyps : funelim.

(** Destruct conjunctions everywhere, starting with the hypotheses.
   This tactic allows to close functional induction proofs involving
   multiple nested and/or mutual recursive definitions. *)

Lemma uncurry_prod (A B C : Type) : (A * B -> C) -> (A -> B -> C).
Proof. intros H a b. exact (H (pair a b)). Defined.

Ltac specialize_mutual_nested := 
  match goal with
  | [ H : _ * _ |- _ ] => destruct H
  | [ |- _ * _ ] => split
  end.

#[export] Hint Extern 50 => specialize_mutual_nested : funelim.

Ltac specialize_mutual :=
  match goal with
    [ H : _ * _ |- _ ] => destruct H
  (* Fragile, might render later goals unprovable *)
  | [ H : ?X -> _, H' : ?X |- _ ] =>
    match X with
      | forall (_ : _), _ => specialize (H H')
    end
  | [ H : (?A * ?B) -> ?C |- _ ] => apply (uncurry_prod A B C) in H
  end.

Ltac Equations.Init.specialize_mutfix ::= repeat specialize_mutual.
