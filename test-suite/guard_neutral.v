(* Regression tests for dependent equality simplification under the
   neutral-head guard checking of rocq-prover/rocq#22142. *)
Module VectorTail.
From Stdlib Require Import Arith Vectors.Vector.
From Equations.Prop Require Import Equations.
Import Sigma_Notations.

Definition eta_vector {A} (P : forall n, Vector.t A n -> Type) :
  forall n v,
    match v with
    | Vector.nil _ => P 0 (Vector.nil A)
    | Vector.cons _ a k t => P _ (Vector.cons A a k t)
    end = P n v.
Proof. now destruct v. Defined.

Definition length {X : Type} :
  forall m n (xs : Vector.t X (m + n)), nat.
Proof.
  fix IH 3. intros m n xs.
  eassert ?[ty].
  refine (
    match xs as xs' in Vector.t _ k return
      (match xs' with
       | Vector.nil _ =>
           (0, Vector.nil X) = (m + n, xs) -> nat
       | Vector.cons _ x' n' xs'' =>
           (S n', Vector.cons X x' n' xs'') =
           (m + n, xs) -> nat
       end)
    with
    | Vector.nil _ => _
    | Vector.cons _ x k tail => _
    end).
  - destruct m as [|m']; simpl; simplify *.
    exact 0.
  - destruct m as [|m']; simpl; simplify *.
    exact 0.
    exact (S (IH m' n tail)).
  - rewrite
      (eta_vector (fun nv v => (nv, v) = (m + n, xs) -> nat))
      in X0.
    exact (X0 eq_refl).
Defined.

End VectorTail.

Module RenamingComposition.
From Stdlib Require Import List.
From Equations.Prop Require Import Equations.
Import ListNotations.

Set Equations With UIP.
Set Transparent Obligations.

Inductive Ren : list nat -> list nat -> Set :=
| NoRen : Ren [] []
| Drop {t g h} : Ren g h -> Ren (t :: g) h
| Keep {t g h} : Ren g h -> Ren (t :: g) (t :: h).

Derive Signature NoConfusion EqDec for Ren.

Equations RcR {g h k} (r : Ren h k) (r' : Ren g h) : Ren g k :=
RcR s NoRen := s;
RcR s (Drop d) := Drop (RcR s d);
RcR (Drop s) (Keep d) := Drop (RcR s d);
RcR (Keep s) (Keep d) := Keep (RcR s d).

Check RcR_elim.

End RenamingComposition.
