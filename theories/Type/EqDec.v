(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Warnings "-notation-overridden".

From Equations Require Import Init.
From Equations.Type Require Import Logic.
From Equations.Type Require Import Classes.

(** Decidable equality.

   We redevelop the derivation of [K] from decidable equality on [A] making
   everything transparent and moving to [Type] so that programs using this 
   will actually be computable inside Coq. *)

Set Universe Polymorphism.

Import Id_Notations.
Import Sigma_Notations.
Local Open Scope equations_scope.

(** We rederive the UIP shifting proof transparently, and on type.
    Taken from Coq's stdlib.
 *)

Definition UIP_refl_on_ X (x : X) := forall p : x = x, p = 1.
Definition UIP_refl_ X := forall (x : X) (p : x = x), p = 1.

Lemma Id_trans_r {A} (x y z : A) : x = y -> z = y -> x = z.
Proof.
  destruct 1. destruct 1. exact 1.
Defined.

(** We rederive the UIP shifting proof transparently. *)
Theorem UIP_shift_on@{i} (X : Type@{i}) (x : X) :
  UIP_refl_on_ X x -> forall y : x = x, UIP_refl_on_ (x = x) y.
Proof.
  intros UIP_refl y.
  rewrite (UIP_refl y).
  intros z.
  assert (UIP:forall y' y'' : x = x, y' = y'').
  { intros. apply Id_trans_r with 1; apply UIP_refl. }
  transitivity (id_trans (id_trans (UIP 1 1) z)
                         (id_sym (UIP 1 1))).
  - destruct z. destruct (UIP _ _). reflexivity.
  - change
      (match 1 as y' in _ = x' return y' = y' -> Type@{i} with
       | 1 => fun z => z = 1
       end (id_trans (id_trans (UIP 1 1) z)
                     (id_sym (UIP (1) (1))))).
    destruct z. destruct (UIP _ _). reflexivity.
Defined.

Theorem UIP_shift@{i} : forall {U : Type@{i}}, UIP_refl_@{i} U -> forall x:U, UIP_refl_@{i} (x = x).
Proof. exact (fun U UIP_refl x => @UIP_shift_on U x (UIP_refl x)). Defined.

(** This is the reduction rule of UIP. *)
Lemma uip_refl_refl@{i} {A : Type@{i}} {E : UIP@{i} A} (x : A) : uip (x:=x) 1 1 = 1.
Proof.
  apply UIP_shift@{i}.
  intros y e. apply uip@{i}.
Defined.

Theorem UIP_K@{i j} {A : Type@{i}} {U : UIP A} (x : A) :
  forall P : x = x -> Type@{j},
    P 1 -> forall p : x = x, P p.
Proof.
  intros P peq e. now elim (uip 1 e).
Defined.

(** Tactic to solve EqDec goals, destructing recursive calls for the recursive 
  structure of the type and calling instances of eq_dec on other types. *)

Ltac eqdec_loop t u :=
  (left; reflexivity) || 
  (solve [right; intro He; inversion He]) ||
  (let x := match t with
             | context C [ _ ?x ] => constr:(x)
             end
    in
    let y := match u with
             | context C [ _ ?y ] => constr:(y)
             end
    in
    let contrad := let Hn := fresh in
                   intro Hn; right; intro He; apply Hn; inversion He; reflexivity in
    let good := intros ->;
      let t' := match t with
                | context C [ ?x _ ] => constr:(x)
                end
      in
      let u' := match u with
                | context C [ ?y _ ] => constr:(y)
                end
      in
      (* idtac "there" t' u'; *)  try (eqdec_loop t' u')
    in
    (* idtac "here" x y; *)
    match goal with
    | [ H : forall z, sum (Id _ z) _ |- _ ] =>
      case (H y); [good|contrad]
    | _ => case (eq_dec x y); [good|contrad]
    end) || idtac.

Ltac eqdec_proof := try red; intros;
  match goal with
   | |- sum (Id ?x ?y) _ =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- sum (Id ?x ?y) _ => eqdec_loop x y
    end
  end.

(** Derivation of principles on sigma types whose domain is decidable. *)

Section EqdepDec.
  Universe  i.
  Context {A : Type@{i}} `{EqDec A}.

  Let comp {x y y':A} (eq1:x = y) (eq2:x = y') : y = y' :=
    Id_rect _ _ (fun a _ => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = id_refl y.
  Proof.
    intros.
    case u; compute. apply id_refl.
  Defined.

  Variable x : A.

  Let nu {y:A} (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => Empty_rect (fun _ => _) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
  Proof. 
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case e; trivial.
  Defined.

  Let nu_inv {y:A} (v:x = y) : x = y := comp (nu (id_refl x)) v.

  Remark nu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply trans_sym_eq.
  Defined.

  Theorem eq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv with (u := p1).
    elim nu_left_inv with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Defined.    
  
  Theorem K_dec :
    forall P:x = x -> Type@{i}, P (id_refl x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (id_refl x) p.
    trivial.
  Defined.

  Lemma eq_dec_refl : eq_dec x x = inl (id_refl x).
  Proof.
    case eq_dec; intros. apply ap. apply eq_proofs_unicity. 
    elim e. apply id_refl.
  Defined.

  (** The corollary *)
  (* On [sigma] *)
  
  Let projs {P:A -> Type@{i}} (exP:sigma P) (def:P x) : P x :=
    match exP with
      | sigmaI _ x' prf =>
        match eq_dec x' x with
          | inl eqprf => Id_rect _ x' (fun x _ => P x) prf x eqprf
          | _ => def
        end
    end.

  Theorem inj_right_sigma {P : A -> Type@{i}} {y y':P x} :
      (x, y) = (x, y') -> y = y'.
  Proof.
    intros.
    cut (projs (x, y) y = projs (sigmaI P x y') y).
    unfold projs. 
    case (eq_dec x x).
    intro e.
    elim e using K_dec. trivial.

    intros.
    case e; reflexivity.

    case X; reflexivity.
  Defined.

  Lemma inj_right_sigma_refl (P : A -> Type@{i}) (y : P x) :
    inj_right_sigma (y:=y) (y':=y) 1 = (id_refl _).
  Proof.
    unfold inj_right_sigma. intros.
    unfold eq_rect. unfold projs.
    destruct (id_sym@{i} eq_dec_refl).
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst projs.
    simpl. unfold nu_inv, comp, nu. simpl.
    unfold eq_ind, nu_left_inv, trans_sym_eq, eq_rect, nu_constant.
    destruct (id_sym@{i} eq_dec_refl). reflexivity.
  Defined.

End EqdepDec.

Definition transport {A : Type} {P : A -> Type} {x y : A} (p : x = y) : P x -> P y :=
  match p with id_refl => fun h => h end.

Lemma sigma_eq@{i} (A : Type@{i}) (P : A -> Type@{i}) (x y : sigma P) :
  x = y -> Σ p : (x.1 = y.1), transport p x.2 = y.2.
Proof.
  intros H; destruct H.
  destruct x as [x px]. simpl.
  refine (id_refl, id_refl).
Defined.  

Theorem inj_sigma_r@{i} {A : Type@{i}} `{H : HSet A} {P : A -> Type@{i}} {x} {y y':P x} :
    sigmaI P x y = sigmaI P x y' -> y = y'.
Proof.
  intros [H' H'']%sigma_eq. cbn in *.
  pose (is_hset H' id_refl).
  apply (transport (P:=fun h => transport h y = y') i H'').
Defined.

Definition apd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) :
  transport p (f x) = f y.
Proof. now destruct p. Defined.

Definition apd_eq {A} {x y : A} (p : x = y) {z} (q : z = x) :
  transport (P:=@Id A z) p q = id_trans q p.
Proof. now destruct p, q. Defined.

Lemma id_trans_sym {A} (x y z : A) (p : x = y) (q : y = z) (r : x = z) :
  id_trans p q = r -> q = id_trans (id_sym p) r.
Proof. destruct p, q. destruct 1. exact 1. Defined.

Lemma hprop_hset {A} (h : HProp A) : HSet A.
Proof.
  intro x.
  set (g y := h x y).
  intros y z w.
  assert (forall y z (p : y = z), p = id_trans (id_sym (g y)) (g z)).
  intros. apply id_trans_sym. destruct (apd_eq p (g y0)). apply apd.
  rewrite X. now rewrite (X _ _ z).
Defined.

(** Proof that equality proofs in 0-truncated types are connected *)
Lemma hset_pi {A} `{HSet A} (x y : A) (p q : x = y) (r : p = q) : is_hset p q = r.
Proof.
  red in H.
  pose (hprop_hset (H x y)).
  apply h.
Defined.

Lemma is_hset_refl {A} `{HSet A} (x : A) : is_hset (id_refl x) id_refl = id_refl.
Proof.
  apply hset_pi.
Defined.  

Lemma inj_sigma_r_refl@{i} (A : Type@{i}) (H : HSet A) (P : A -> Type@{i}) x (y : P x) :
  inj_sigma_r (y:=y) (y':=y) 1 = (id_refl _).
Proof.
  unfold inj_sigma_r. intros.
  simpl. now rewrite is_hset_refl.
Defined.

Theorem K {A} `{HSet A} (x : A) (P : x = x -> Type) :
  P (id_refl x) -> forall p : x = x, P p.
Proof.
  intros. exact (transport (is_hset id_refl p) X).
Defined.
