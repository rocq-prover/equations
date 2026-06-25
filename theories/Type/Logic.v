From Equations Require Import Init.
From Stdlib Require Import Extraction CRelationClasses.

Set Warnings "-notation-overridden".

(** The polymorphic equality type used by Equations when working with equality in Type. *)

Set Universe Polymorphism.

(* Let's leave empty at Set, it can live in any higher universe. *)
Inductive Empty : Set :=.

Scheme Empty_case := Minimality for Empty Sort Type.

Definition unit_rect@{i} (P : unit -> Type@{i}) (p : P tt) (u : unit) : P u :=
  match u with tt => p end.

Definition prod (A : Type) (B : Type) := sigma (fun _ : A => B).

Notation " A * B " := (prod A B) : type_scope.

Definition BiImpl (A B : Type) : Type := (A -> B) * (B -> A).

Notation "A <-> B" := (BiImpl A B) (at level 95) : type_scope.

Cumulative Inductive Id@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
  id_refl : Id a a.
Arguments id_refl {A a}, [A] a.

Scheme Rewriting for Id.
Arguments Id_rew {A}.
Arguments Id_rew_r {A}.

Local Open Scope equations_scope.

Module Id_Notations.
  Notation " x = y " := (@Id _ x y) : equations_scope.
  Notation " x = y " := (@Id _ x y) : type_scope.
  Notation " x <> y " := (@Id _ x y -> Empty) : equations_scope.
  Notation " x <> y " := (@Id _ x y -> Empty) : type_scope.
  Notation " 1 " := (@id_refl _ _) : equations_scope.
End Id_Notations.

Import Id_Notations.

Module Sigma_Notations.

Notation "'Σ' x .. y , P" := (sigma (fun x => .. (sigma (fun y => P)) ..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
      (right associativity, at level 0,
       format "( x ,  .. ,  y ,  z )") : equations_scope.

Notation "x .1" := (pr1 x) : equations_scope.
Notation "x .2" := (pr2 x) : equations_scope.

End Sigma_Notations.

Import Sigma_Notations.

Section IdTheory.
  Universe i.
  Context {A : Type@{i}}.

  Import Id_Notations.

  Lemma id_sym {x y : A} : x = y -> y = x.
  Proof. destruct 1. apply 1. Defined.

  Lemma id_trans {x y z : A} : x = y -> y = z -> x = z.
  Proof. destruct 1. destruct 1. apply 1. Defined.

  Definition transport (x : A) (P : A -> Type) : P x -> forall y : A, Id x y -> P y.
  Proof. intros Px y e. destruct e. exact Px. Defined.

  Definition Id_case (P : A -> Type) {x y : A} : Id y x -> P x -> P y.
  Proof. intros e Px. eapply (transport x _ Px y (id_sym e)). Defined.
  
  Lemma Id_rect_r {x : A} (P : forall a, Id a x -> Type) (p : P x id_refl)
        {y : A} (e : Id y x) : P y e.
  Proof. destruct e. apply p. Defined.

  Import Sigma_Notations.
  Definition id_inspect (x : A) : Σ y , x = y := (x , 1).
End IdTheory.

Class HProp A := is_hprop : forall x y : A, x = y.

Class HSet A := is_hset : forall {x y : A}, HProp (x = y).

Cumulative Inductive sum@{i} (A : Type@{i}) (B : Type@{i}) :=
| inl : A -> A + B
| inr : B -> A + B
where " A + B " := (sum A B) : type_scope.

Arguments inl {A} {B} a.
Arguments inr {A} {B} b.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
  match p with 1 => 1 end.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
Arguments eisretr {A B}%_type_scope f%_function_scope {_} _.
Arguments eissect {A B}%_type_scope f%_function_scope {_} _.
Arguments eisadj {A B}%_type_scope f%_function_scope {_} _.
Arguments IsEquiv {A B}%_type_scope f%_function_scope.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _.

Declare Scope equiv_scope.
Bind Scope equiv_scope with Equiv.

Reserved Infix "<~>" (at level 85).
Notation "A <~> B" := (Equiv A B) (at level 85) : type_scope.

Notation "f ^^-1" := (@equiv_inv _ _ f _) (at level 1).
