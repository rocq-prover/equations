(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Warnings "-notation-overridden".

From Equations Require Import Init.
From Equations.HoTT Require Import Logic Classes.

(** Decidable equality.

   We redevelop the derivation of [K] from decidable equality on [A] making
   everything transparent and moving to [Type] so that programs using this 
   will actually be computable inside Coq. *)

Set Universe Polymorphism.

Import Sigma_Notations.
Local Open Scope equations_scope.
Local Open Scope path_scope.

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
  transitivity (concat (concat (UIP 1 1) z)
                         (inverse (UIP 1 1))).
  - destruct z. destruct (UIP _ _). reflexivity.
  - change
      (match 1 as y' in _ = x' return y' = y' -> Type@{i} with
       | 1 => fun z => z = 1
       end (concat (concat (UIP 1 1) z)
                     (inverse (UIP (1) (1))))).
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
  intros P peq e. elim (uip 1 e); assumption.
Defined.

(** Derivation of principles on sigma types whose domain is decidable. *)

Section EqdepDec.
  Universe  i.
  Context {A : Type@{i}} `{EqDec A}.

  Let comp {x y y':A} (eq1:x = y) (eq2:x = y') : y = y' :=
    paths_ind _ (fun a _ => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = @idpath _ y.
  Proof.
    intros. case u; compute. exact 1.
  Defined.

  Variable x : A.

  Let nu {y:A} (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => Empty_rect (fun _ => _) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    - exact 1.
    - case e; trivial.
  Defined.

  Let nu_inv {y:A} (v:x = y) : x = y := comp (nu 1) v.

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
    forall P:x = x -> Type@{i}, P 1 -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x 1 p.
    trivial.
  Defined.

  Lemma eq_dec_refl : eq_dec x x = inl 1.
  Proof.
    case eq_dec; intros.
    - apply ap. apply eq_proofs_unicity.
    - elim e. apply 1.
  Defined.

  (** The corollary *)
  (* On [sigma] *)
  
  Let projs {P:A -> Type@{i}} (exP:sigma P) (def:P x) : P x :=
    match exP with
      | sigmaI x' prf =>
        match eq_dec x' x with
          | inl eqprf => paths_ind x' (fun x _ => P x) prf x eqprf
          | _ => def
        end
    end.

  Theorem inj_right_sigma {P : A -> Type@{i}} {y y':P x} :
      (x, y) = (x, y') -> y = y'.
  Proof.
    intros.
    cut (projs (x, y) y = projs (sigmaI P x y') y).
    - unfold projs.
      case (eq_dec x x).
      -- intro e.
         elim e using K_dec. trivial.
      -- intros.
         case e; reflexivity.
    - case X; reflexivity.
  Defined.

  Lemma inj_right_sigma_refl (P : A -> Type@{i}) (y : P x) :
    inj_right_sigma (y:=y) (y':=y) 1 = 1.
  Proof.
    unfold inj_right_sigma. intros.
    unfold paths_ind. unfold projs.
    destruct (inverse@{i} eq_dec_refl).
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst projs.
    simpl. unfold nu_inv, comp, nu. simpl.
    unfold paths_ind, nu_left_inv, trans_sym_eq, paths_rect, nu_constant.
    destruct (inverse@{i} eq_dec_refl). reflexivity.
  Defined.

End EqdepDec.


#[export]
Instance eq_eqdec {A} `{EqDec A} : forall x y : A, EqDec (x = y).
Proof.
  intros. red. intros.
  exact (inl (eq_proofs_unicity _ _ x0 y0)).
Defined.

#[export]
Instance eqdec_uip {A} (E : EqDec A) : UIP A :=
  fun x y e e' => eq_proofs_unicity _ _ e e'.

#[export]
Instance eq_uip {A} (E : UIP A) : forall x : A, UIP (x = x).
Proof.
  intros y e e'. intros e''. destruct e''.
  assert (Us := @UIP_shift A). compute in Us. forward Us.
  - intros; apply E.
  - intros. apply inverse. apply Us.
Qed.

#[export]
Instance eqdec_hset (A : Type) `(UIP A) : IsHSet A.
Proof.
  constructor.
  intros x y. constructor. intros p q.
  eapply Build_Contr with (uip p q). intros e.
  destruct p. apply uip.
Defined.

Lemma sigma_eq@{i} (A : Type@{i}) (P : A -> Type@{i}) (x y : sigma P) :
  x = y -> Σ p : (x.1 = y.1), p # x.2 = y.2.
Proof.
  intros H; destruct H.
  destruct x as [x px]. simpl.
  refine (1, 1).
Defined.  

Lemma is_hset {A} `{H : IsHSet A} {x y : A} (p q : x = y) : p = q.
Proof.
  apply HSet.hset_path2.
Defined.

Theorem inj_sigma_r@{i} {A : Type@{i}} `{H : IsHSet A} {P : A -> Type@{i}} {x} {y y':P x} :
    sigmaI P x y = sigmaI P x y' -> y = y'.
Proof.
  intros [H' H'']%sigma_eq. cbn in *.
  pose (i := is_hset H' 1).
  apply (transport (fun h => transport _ h y = y') i H'').
Defined.

Definition apd_eq {A} {x y : A} (p : x = y) {z} (q : z = x) :
  transport (@paths A z) p q = q @ p.
Proof. destruct p, q; reflexivity. Defined.

From HoTT Require Import Basics.Trunc.

Lemma hprop_hset {A} (h : IsHProp A) : IsHSet A.
Proof.
  apply istrunc_hprop.
Defined.

(** Proof that equality proofs in 0-truncated types are connected *)
Lemma hset_pi {A} `{H : IsHSet A} (x y : A) (p q : x = y) (r : p = q) : is_hset p q = r.
Proof.
  pose (hprop_hset (H x y)).
  unfold is_hset.
  apply HSet.hset_path2.
Defined.

Lemma is_hset_refl {A} `{H : IsHSet A} (x : A) : is_hset (@idpath _ x) 1 = 1%path.
Proof.
  apply hset_pi.
Defined.

Lemma inj_sigma_r_refl@{i} (A : Type@{i}) (H : IsHSet A) (P : A -> Type@{i}) x (y : P x) :
  inj_sigma_r (y:=y) (y':=y) 1 = 1%path.
Proof.
  unfold inj_sigma_r. intros.
  simpl.
  rewrite HSet.axiomK_idpath; trivial.
Defined.

Theorem K {A} `{IsHSet A} (x : A) (P : x = x -> Type) :
  P 1%path -> forall p : x = x, P p.
Proof.
  intros. exact (is_hset 1 p # X).
Defined.
