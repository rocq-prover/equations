(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Signatures for dependent types. 
   
   A signature for [A] is a sigma-type in which any [A] 
   can be packed. *)

From Equations Require Import Init.

Polymorphic Class Signature@{i} (fam : Type@{i}) (signature_index : Type@{i})
            (signature : forall (_ : signature_index), Type@{i}) : Type@{i} :=
  signature_pack : forall (_ : fam), sigma signature.
#[global]
Hint Mode Signature ! - - : typeclass_instances.

Polymorphic Definition signature {fam index sig} `{S : @Signature fam index sig} := sig.

Register Equations.Signature.Signature as equations.signature.class.
Register Equations.Signature.signature as equations.signature.signature.
Register Equations.Signature.signature_pack as equations.signature.pack.

Extraction Inline signature signature_pack.

(* For right associated sigmas *)

Ltac destruct_right_sigma H :=
  match type of H with
  | @sigma _ (fun x => _) =>
    let H' := fresh H in
    destruct H as [? H']; destruct_right_sigma H'
  | @sigma _ _ =>
    let H' := fresh H in
    destruct H as [? H'];
      destruct_right_sigma H'
  | _ => idtac
  end.

Ltac destruct_one_sigma :=
  match goal with
  | [ H : @sigma _ _ |- _ ] => destruct_right_sigma H
  end.

Ltac simp_sigmas := repeat destruct_one_sigma.
