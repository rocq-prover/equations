(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations.Prop Require Import Equations.

Unset Universe Polymorphism.

Ltac find_noCycle_proof H :=
  let rec aux t ty := 
      match ty with
      | ?x <> ?x => apply (t eq_refl)
      | (?A * ?B)%type => 
        aux (fst t) A || aux (snd t) B
      end
  in simpl in H; let t := type of H in aux H t.

Inductive tree : Set :=
| leaf | node (l r : tree).

Derive NoConfusion for tree.
Derive DependentElimination for tree.
Derive Below for tree.

Local Definition nlt x y := Below_tree (fun y => x <> y) y.
Local Definition nle (x y : tree) := ((x <> y) * nlt x y)%type.

Notation  "x ¬< y " := (nlt x y) (at level 80).
Notation  "x ¬≤ y " := (nle x y) (at level 80).
Lemma noCycle_tree : forall x y : tree, x = y -> nlt x y.
Proof.
  intros x y <-. induction x as [|l Hl r Hr].
  * now simpl.
  * split. 
    { change (nle (node l r) r).
      revert Hr. generalize r at 2 4 as r'. 
      induction r'; intros Hr.

      split; trivial. intro H; noconf H.
      split. 
      + intro Heq; noconf Heq.
        now apply (fst (fst Hr)). 
      + firstorder. }
    { change (nle (node l r) l).
      revert Hl. generalize l at 2 4 as l'.
      induction l'; intros Hl'. 
      split; trivial.
      - now intro H; noconf H.
      - split.
        + intro Heq; noconf Heq;
          firstorder.
        + firstorder. }
Qed.

From Stdlib Require Import CRelationClasses.

#[export]
Instance nlt_refl : Reflexive nlt.
Proof. intros x. now apply noCycle_tree. Defined.
(* Neither transivite nor symmetric *)

Lemma noCycle_test l r : node l r <> r.
Proof.
  intros H; pose proof (noCycle_tree r (node l r) (eq_sym H)). simpl in X.
  find_noCycle_proof X.
Qed.

Lemma noCycle_test2 l r : node (node l l) r <> r.
Proof.
  intros H; pose proof (noCycle_tree _ _ (eq_sym H)).
  find_noCycle_proof X.
Qed.

Lemma noCycle_test3 l r k u : node (node k (node l l)) (node u r) <> r.
Proof.
  intros H; pose proof (noCycle_tree _ _ (eq_sym H)).
  find_noCycle_proof X.
Qed.

Equations build_tree (l r : tree) (n : nat) : tree :=
build_tree l r 0 := node r r;
build_tree l r (S n) := node l (build_tree l r n).
Transparent build_tree.

Lemma noCycle_bigtest l r : build_tree l r 10 <> r.
Proof.
  intros H; pose proof (noCycle_tree _ _ (eq_sym H)).
  find_noCycle_proof X.
Qed.
