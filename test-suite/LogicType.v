Set Warnings "-notation-overridden".

Set Universe Polymorphism.
(** Switch to an equality in Type *)
From Equations.Type Require Import All.

Derive Signature for Id.

Definition nathset := _ : HSet nat.

(* Equations test_k (x : nat) (r : x = x) : r = r := *)
(*   test_k x id_refl := id_refl. *)

Equations foo (A : Type) (x : A) : A :=
foo A x := x.


Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature for fin.

Derive NoConfusion for nat.

Equations finp {n} (f : fin (S n)) : unit + fin n :=
  finp fz := inl tt;
  finp (fs f) := inr f.

Unset Universe Minimization ToSet.
Inductive vector@{i} (A : Type@{i}) : nat -> Type@{i} :=
| nil : vector A 0
| cons {n : nat} : A -> vector A n -> vector A (S n).
Arguments vector A%_type_scope n%_nat_scope.
Arguments nil {A}.
Arguments cons {A%_type_scope} {n%_nat_scope} a v.
Derive Signature for vector.
From Equations Require Import CoreTactics.
From Equations.Type Require Import Tactics FunctionalInduction.

Set Universe Minimization ToSet.
Derive NoConfusionHom for vector.

Print NoConfusionHomPackage_vector.
Unset Universe Minimization ToSet.

#[export]
Instance vector_eqdec@{i} {A : Type@{i}} {n} `(EqDec@{i} A) : EqDec@{i} (vector@{i} A n).
Proof.
  intros. intros x. intros y. induction x.
  - left. now depelim y.
  - depelim y.
    pose proof (Classes.eq_dec a a0).
    dependent elimination X as [inl id_refl|inr Ha].
    -- specialize (IHx v). 
        dependent elimination IHx as [inl id_refl|inr H'].
        --- left; reflexivity.
        --- right. simplify *. now apply H'.
    -- right; simplify *. now apply Ha.
Defined.

Record vect {A} := mkVect { vect_len : nat; vect_vector : vector A vect_len }.
Coercion mkVect : vector >-> vect.
Set Universe Minimization ToSet.

Derive NoConfusion for vect.
Reserved Notation "x ++v y" (at level 60).

Equations vapp {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m)%nat :=
{ nil ++v w := w ;
  (cons a v) ++v w := cons a (v ++v w) }
where "x ++v y" := (vapp x y).

Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type :=
  append : forall (xs : vector X m)(ys : vector X n), Split (vapp xs ys).

Arguments Split [ X ].

(* Eval compute in @app'. *)
(* About nil. About vector. *)
(* Set Typeclasses Debug Verbosity 2. *)
(* Set Typeclasses Filtered Unification. *)

#[local] Hint Extern 0 (WellFounded _) => refine WellFoundedInstances.lt_wf : typeclass_instances.

Equations split {X : Type} {m n : nat} (xs : vector X (Peano.plus m n)) : Split m n xs by wf m :=
split (m:=0) xs := append nil xs;
split (m:=S m) (cons x xs) with split xs => {
  | append xs' ys' := append (cons x xs') ys' }.

Derive Subterm for vector.
#[local] Hint Unfold vector_subterm : subterm_relation.

Import Sigma_Notations.
Section foo.
  Context {A B : Type}.
  Equations unzipv {n} (v : vector (A * B) n) : vector A n * vector B n
   by wf (signature_pack v) (@vector_subterm (A * B)) :=
  unzipv nil := (nil, nil) ;
  unzipv (cons (x, y) v) with unzipv v := {
    | (xs, ys) := (cons x xs, cons y ys) }.
End foo.

Set Universe Minimization ToSet.
Section vlast.
  Context {A : Type}.
  Equations vlast {n} (v : vector A (S n)) : A by wf (signature_pack v) (@vector_subterm A) :=
  vlast (cons (n:=O) a nil) := a ;
  vlast (cons (n:=S n') a v) := vlast v.
End vlast.
