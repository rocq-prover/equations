(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Stdlib Require Import Program.
From Equations.Prop Require Import Equations.

From Stdlib Require Import Utf8 Lia Arith.

From Stdlib Require Import List.
Import ListNotations.

Set Keyed Unification.

Equations map_In {A B : Type}
     (l : list A) (f : forall (x : A), In x l -> B) : list B :=
  | nil, _ := nil
  | cons x xs, f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  funelim (map_In l _); rewrite ?H; trivial.
Qed.
  
Section list_size.
  Context {A : Type} (f : A -> nat).
  Equations list_size (l : list A) : nat :=
   | nil := 0
   | x :: xs := S (f x + list_size xs).
  
  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size xs).
  Proof.
    intros. funelim (list_size xs); simpl in *. destruct H.
    destruct H0.
    * subst; lia.
    * specialize (H _ H0). intuition. lia.
  Qed.
End list_size.
Transparent list_size.

Scheme All for list.

Module RoseTree.

  Section roserec.
    Context {A : Set}.

    Inductive t : Set :=
    | leaf (a : A) : t
    | node (l : list t) : t.
    Derive NoConfusion for t.

    Fixpoint size (r : t) :=
      match r with
      | leaf a => 0
      | node l => S (list_size size l)
      end.

    Equations? elements (r : t) : list A by wf (size r) lt :=
    elements (leaf a) := [a];
    elements (node l) := concat (map_In l (fun x H => elements x)).
    Proof. red. now apply In_list_size. Qed.
      
    Equations elements_def (r : t) : list A :=
    elements_def (leaf a) := [a];
    elements_def (node l) := concat (List.map elements_def l).
    Lemma elements_equation (r : t) : elements r = elements_def r.
    Proof.
      funelim (elements r); simp elements_def; trivial. f_equal.
      rewrite map_In_spec. clear Heqcall.
      induction l; simpl; auto. rewrite H. rewrite IHl; auto.
      intros. apply H. now constructor 2. now constructor.
    Qed.

    (** To solve measure subgoals *)
    Hint Extern 4 (_ < _) => simpl; lia : rec_decision.
    Hint Extern 4 (MR _ _ _ _) => repeat red; simpl in *; lia : rec_decision.

    Obligation Tactic := simpl in *; program_simpl; try typeclasses eauto with subterm_relation simp rec_decision.

    (* Nested rec *) 
    Equations elements_acc (r : t) (acc : list A) : list A by wf (size r) lt :=
    elements_acc (leaf a) acc := a :: acc;
    elements_acc (node l) acc := aux l _
      where aux (x : list t) (H : list_size size x < size (node l)) : list A by wf (list_size size x) lt :=
      aux nil _ := acc;
      aux (cons x xs) H := elements_acc x (aux xs _).

    Definition elements2 (r : t) : list A := elements_acc r [].

    Lemma elements2_equation r acc : elements_acc r acc = elements_def r ++ acc.
    Proof.
      revert r acc.
      let t := constr:(fun_elim (f:=elements_acc)) in
      apply (t (fun r acc res => res = elements_def r ++ acc)
               (fun r acc x H res => res = concat (List.map elements_def x) ++ acc));
        intros; simp elements; trivial.
      rewrite H1. clear H1.
      rewrite H0. simpl. now rewrite app_assoc.
    Qed.

    Equations elements' (r : t) : list A by wf r (MR lt size) :=
     | leaf a := [a]
     | node l := fn l hidebody

    where fn (x : list t) (H : list_size size x < size (node l)) : list A
      by wf x (MR lt (list_size size)) :=
     | nil, _ := nil;
      | cons x xs, _ := elements' x ++ fn xs hidebody.

    Equations elements'_def (r : t) : list A :=
    elements'_def (leaf a) := [a];
    elements'_def (node l) := concat (List.map elements' l).

    Lemma elements'_equation (r : t) : elements' r = elements'_def r.
    Proof.
      pose (fun_elim (f:=elements')).
      apply (p (fun r f => f = elements'_def r) (fun l x H r => r = concat (List.map elements' x)));
        clear p; intros; simp elements'_def; trivial.
      simpl. f_equal. apply H1.
    Qed.
    
  End roserec.
  Arguments t : clear implicits.

  Section AltSize.
    Context {A : Set}.

    (** Let's use an alternative size criterion allowing to make recursive calls
        on non-strict subterms of the initial list: we just count the maximal
        depth of [node] constructors among all forests. *)
    Equations alt_size (r : t A) : nat :=
    { alt_size (leaf _) => 0;
      alt_size (node l) => S (max_size l) }
    where max_size (l : list (t A)) : nat :=
    { max_size nil := 0;
      max_size (cons a t) := Nat.max (alt_size a) (max_size t) }.

    (** This has the property that the maximal size of two appended lists is the maximal
        size of the separate lists. *)
    Lemma max_size_app l l' : max_size (l ++ l') = Nat.max (max_size l) (max_size l').
    Proof.
      induction l; simp max_size. reflexivity.
      simpl. rewrite <- Nat.max_assoc. f_equal.
      apply IHl.
    Qed.

    Context {B : Set} (f : A -> B).

    (** It hence becomes possible to recurse on an arbitrary list as long as the depth
        decreases, for example by appending the subforest to itself in the [node] case.
        The same is possible with sized types where node has type [j < i -> list^i (t^j) -> t^(S i)].
     *)
    Equations? map_t (r : t A) : t B by wf (alt_size r) lt :=
      map_t (leaf a) := leaf (f a);
      map_t (node l) := node (map_list (l ++ l) _)

      where map_list (l' : list (t A)) (H : max_size l' ≤ max_size l) : list (t B) by struct l' :=
      map_list nil _ := nil;
      map_list (cons a t) Hl' := cons (map_t a) (map_list t _).
    Proof. simp alt_size. apply Nat.lt_succ_r. now apply Nat.max_lub_l in Hl'.
           now apply Nat.max_lub_r in Hl'.
           clear map_list. rewrite max_size_app. now rewrite Nat.max_id.
    Defined.
  End AltSize.

  Section fns.
    Context {A B : Set} (f : A -> B) (g : B -> A -> B) (h : A -> B -> B).
    
    Equations map (r : t A) : t B :=
      | leaf a := leaf (f a)
      | node l := node (List.map map l).

    Equations fold (acc : B) (r : t A) : B :=
    fold acc (leaf a) := g acc a;
    fold acc (node l) := List.fold_left fold l acc.

    Equations fold_right (r : t A) (acc : B) : B :=
    fold_right (leaf a) acc := h a acc;
    fold_right (node l) acc := List.fold_right fold_right acc l.
  End fns.    

End RoseTree.
