From Equations Require Import Init.

Require Export HoTT.Basics.Overture.
Require Export HoTT.Basics.Tactics.

Set Warnings "-notation-overridden".
Set Universe Polymorphism.

(** Fixes to the HoTT library *)

Register idpath as core.identity.refl.
Register paths_rect as core.identity.ind.
Register paths as core.identity.type.
Register inverse as core.identity.sym.

(** This allows [rewrite] to both in left-to-right and right-to left directions. *)
Definition paths_rect_r (A : Type) (x : A) (P : A -> Type) (p : P x) (y : A) (e : paths y x) : P y :=
  paths_rect A x (fun y e => P y) p y (inverse e).
Register concat as core.identity.trans.

Register ap as core.identity.congr.

(** [path_inspect x] allows to pattern-match x while retaining a propositional equality with [x] *)

Definition path_inspect {A : Type} (x : A) : { y | paths x y } := (x ; idpath).

From HoTT Require Import Types.Bool.
(* For compatibility with Coq's [induction] *)
Definition Bool_rect := Bool_ind.

(** /End of fixes to the HoTT library *)

(** The polymorphic equality type used by Equations when working with equality in Type. *)

Definition transport_r {A} (P : A -> Type) {x y : A} (e : y = x) : P x -> P y :=
  fun x => match (inverse e) with 1%path => x end.

Lemma paths_rect_dep_r {A} (x : A) (P : forall a, a = x -> Type) (p : P x 1%path)
      (y : A) (e : y = x) : P y e.
Proof. destruct e. apply p. Defined.

Module Sigma_Notations.

Notation "'Σ' x .. y , P" := (sigma (fun x => .. (sigma (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
      (right associativity, at level 0,
       format "( x ,  .. ,  y ,  z )") : equations_scope.

Notation "x .1" := (Equations.Init.pr1 x) : equations_scope.
Notation "x .2" := (Equations.Init.pr2 x) : equations_scope.

End Sigma_Notations.

Import Sigma_Notations.

Tactic Notation "now" tactic(tac) := tac; solve [ trivial ].
