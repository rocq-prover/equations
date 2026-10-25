(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Names
open EConstr

val hyps_of_vars :
  env -> Evd.evar_map ->
  named_context ->
  Id.Set.t -> Id.Set.t -> Id.Set.elt list

exception Seen

val linear : Evd.evar_map -> Id.Set.t -> constr array -> bool

val needs_generalization :
  Proofview.Goal.t -> Id.t -> bool

val dependent_pattern :
  ?pattern_term:bool -> constr -> unit Proofview.tactic


val depcase
  :  poly:PolyFlags.t
  -> inductive * EInstance.t
  -> Environ.env * Evd.evar_map * rel_context * constr * Names.GlobRef.t

val derive_dep_elimination
  :  Environ.env
  -> Evd.evar_map
  -> poly:PolyFlags.t
  -> inductive * EInstance.t
  -> Constant.t * (Evd.evar_map * constr)

val pattern_call :
  ?pattern_term:bool -> constr -> unit Proofview.tactic

val specialize_eqs : ?with_block:int -> Names.Id.t -> unit Proofview.tactic

val compare_upto_variables : Evd.evar_map -> constr -> constr -> bool

(** When [loc] is given and no patterns are, a warning [dependent-elimination-patterns]
    suggests the patterns inferred for an equivalent [dependent elimination id as [...]] call. *)
val dependent_elim_tac : ?loc:Loc.t -> ?patterns:Syntax.user_pat_loc list -> Names.Id.t Syntax.with_loc ->
  unit Proofview.tactic

val dependent_elim_tac_expr : ?patterns:Constrexpr.constr_expr list -> Names.Id.t Syntax.with_loc ->
  unit Proofview.tactic
