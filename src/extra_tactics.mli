(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Additional general purpose tactics *)

val decompose_app : Names.Id.t -> Names.Id.t -> EConstr.t -> unit Proofview.tactic

val autounfold_ref : Names.GlobRef.t -> unit Proofview.tactic

(** [refine_ho c]

  Matches a lemma [c] of type [∀ ctx, ty] with a conclusion of the form
  [∀ ctx, ?P args] using second-order matching on the problem
  [ctx |- ?P args = ty] and then refines the goal with [c]. *)

val refine_ho : EConstr.t -> unit Proofview.tactic

(** Introduce the next hypothesis reusing the binder name verbatim (modulo
    freshening by subscripts), bypassing name mangling ([Mangle Names]).
    Falls back to [intro] on anonymous binders. *)
val intro_binder_name : unit Proofview.tactic
