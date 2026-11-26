(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Equations Require Import Init.

Set Warnings "-notation-overridden".
From Equations Require Import HoTT.Logic.
Require Export HoTT.Basics.Iff.

Local Open Scope equations_scope.

Import Sigma_Notations.

(** Relations in Type *)
Set Universe Polymorphism.

(** ** Transitive closure *)

Section Transitive_Closure.
  Context {A : Type} (R : Relation A).

  (** Definition by direct transitive closure *)

  Inductive trans_clos (x: A) : A -> Type :=
    | t_step (y:A) : R x y -> trans_clos x y
    | t_trans (y z:A) : trans_clos x y -> trans_clos y z -> trans_clos x z.

  (** Alternative definition by transitive extension on the left *)

  Inductive trans_clos_1n (x: A) : A -> Type :=
    | t1n_step (y:A) : R x y -> trans_clos_1n x y
    | t1n_trans (y z:A) : R x y -> trans_clos_1n y z -> trans_clos_1n x z.

  (** Alternative definition by transitive extension on the right *)

  Inductive trans_clos_n1 (x: A) : A -> Type :=
    | tn1_step (y:A) : R x y -> trans_clos_n1 x y
    | tn1_trans (y z:A) : R y z -> trans_clos_n1 x y -> trans_clos_n1 x z.

End Transitive_Closure.

(** ** Reflexive closure *)

Section Reflexive_Closure.
  Context {A : Type} (R : Relation A).

  (** Definition by direct transitive closure *)

  Inductive clos_refl (x: A) : A -> Type :=
    | r_step (y:A) : R x y -> clos_refl x y
    | r_refl : clos_refl x x.

End Reflexive_Closure.

(** ** Reflexive-transitive closure *)

Section Reflexive_Transitive_Closure.
  Context {A : Type} (R : Relation A).

  (** Definition by direct reflexive-transitive closure *)

  Inductive clos_refl_trans (x:A) : A -> Type :=
    | rt_step (y:A) : R x y -> clos_refl_trans x y
    | rt_refl : clos_refl_trans x x
    | rt_trans (y z:A) :
          clos_refl_trans x y -> clos_refl_trans y z -> clos_refl_trans x z.

  (** Alternative definition by transitive extension on the left *)

  Inductive clos_refl_trans_1n (x: A) : A -> Type :=
    | rt1n_refl : clos_refl_trans_1n x x
    | rt1n_trans (y z:A) :
         R x y -> clos_refl_trans_1n y z -> clos_refl_trans_1n x z.

  (** Alternative definition by transitive extension on the right *)

 Inductive clos_refl_trans_n1 (x: A) : A -> Type :=
    | rtn1_refl : clos_refl_trans_n1 x x
    | rtn1_trans (y z:A) :
        R y z -> clos_refl_trans_n1 x y -> clos_refl_trans_n1 x z.

End Reflexive_Transitive_Closure.

(** ** Reflexive-symmetric-transitive closure *)

Section Reflexive_Symmetric_Transitive_Closure.
  Context {A : Type} (R : Relation A).

  (** Definition by direct reflexive-symmetric-transitive closure *)

  Inductive clos_refl_sym_trans : Relation A :=
    | rst_step (x y:A) : R x y -> clos_refl_sym_trans x y
    | rst_refl (x:A) : clos_refl_sym_trans x x
    | rst_sym (x y:A) : clos_refl_sym_trans x y -> clos_refl_sym_trans y x
    | rst_trans (x y z:A) :
        clos_refl_sym_trans x y ->
        clos_refl_sym_trans y z -> clos_refl_sym_trans x z.

  (** Alternative definition by symmetric-transitive extension on the left *)

  Inductive clos_refl_sym_trans_1n (x: A) : A -> Type :=
    | rst1n_refl : clos_refl_sym_trans_1n x x
    | rst1n_trans (y z:A) : R x y + R y x ->
         clos_refl_sym_trans_1n y z -> clos_refl_sym_trans_1n x z.

  (** Alternative definition by symmetric-transitive extension on the right *)

  Inductive clos_refl_sym_trans_n1 (x: A) : A -> Type :=
    | rstn1_refl : clos_refl_sym_trans_n1 x x
    | rstn1_trans (y z:A) : R y z + R z y ->
         clos_refl_sym_trans_n1 x y -> clos_refl_sym_trans_n1 x z.

End Reflexive_Symmetric_Transitive_Closure.

(** ** Converse of a Relation *)

Section Converse.
  Context {A : Type} (R : Relation A).

  Definition transp (x y:A) := R y x.
End Converse.

(** ** Union of Relations *)

Section Union.
  Context {A : Type} (R1 R2 : Relation A).

  Definition union (x y:A) := (R1 x y + R2 x y)%type.
End Union.

(** ** Disjoint union of Relations *)

Section Disjoint_Union.
  Context {A B : Type}.
  Variable leA : A -> A -> Type.
  Variable leB : B -> B -> Type.

  Inductive le_AsB : A + B -> A + B -> Type :=
  | le_aa (x y:A) : leA x y -> le_AsB (inl x) (inl y)
  | le_ab (x:A) (y:B) : le_AsB (inl x) (inr y)
  | le_bb (x y:B) : leB x y -> le_AsB (inr x) (inr y).

End Disjoint_Union.

(** ** Lexicographic order on dependent pairs *)

Section Lexicographic_Product.
  Context {A : Type} {B : A -> Type}.
  Variable leA : A -> A -> Type.
  Variable leB : forall x:A, B x -> B x -> Type.

  Inductive lexprod : sigma B -> sigma B -> Type :=
    | left_lex :
      forall (x x':A) (y:B x) (y':B x'),
        leA x x' -> lexprod (x, y) (x', y')
    | right_lex :
      forall (x:A) (y y':B x),
        leB x y y' -> lexprod (x, y) (x, y').

End Lexicographic_Product.

(** ** Product of Relations *)

Section Symmetric_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Type.
  Variable leB : B -> B -> Type.

  Inductive symprod : A * B -> A * B -> Type :=
    | left_sym :
      forall x x':A, leA x x' -> forall y:B, symprod (pair x y) (pair x' y)
    | right_sym :
      forall y y':B, leB y y' -> forall x:A, symprod (pair x y) (pair x y').

End Symmetric_Product.

(** ** Multiset of two Relations *)

Section Swap.
  Variable A : Type.
  Variable R : A -> A -> Type.

  Inductive swapprod : A * A -> A * A -> Type :=
    | sp_noswap x y (p:A * A) : symprod A A R R (pair x y) p -> swapprod (pair x y) p
    | sp_swap x y (p:A * A) : symprod A A R R (pair x y) p -> swapprod (pair y x) p.
End Swap.

Local Open Scope equations_scope.
From HoTT Require Import Spaces.List.Core.
Local Open Scope list_scope.

Section Lexicographic_Exponentiation.

  Variable A : Set.
  Variable leA : A -> A -> Type.
  Let Nil := nil (A:=A).
  Let List := list A.

  Inductive Ltl : List -> List -> Type :=
    | Lt_nil (a:A) (x:List) : Ltl Nil (a :: x)
    | Lt_hd (a b:A) : leA a b -> forall x y:list A, Ltl (a :: x) (b :: y)
    | Lt_tl (a:A) (x y:List) : Ltl x y -> Ltl (a :: x) (a :: y).

  Inductive Desc : List -> Type :=
    | d_nil : Desc Nil
    | d_one (x:A) : Desc (x :: Nil)
    | d_conc (x y:A) (l:List) :
        clos_refl leA x y -> Desc (l ++ y :: Nil) -> Desc ((l ++ y :: Nil) ++ x :: Nil).

  Definition Pow : Type := sigma Desc.

  Definition lex_exp (a b:Pow) : Type := Ltl a.1 b.1.

End Lexicographic_Exponentiation.

Create HintDb Relations.
#[export] Hint Unfold transp union: Relations.
#[export] Hint Resolve t_step rt_step rt_refl rst_step rst_refl: Relations.
#[export] Hint Immediate rst_sym: Relations.
