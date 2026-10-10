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
open Equations_common

type peconstructor = Names.constructor peuniverses

(** Internal patterns *)
type pat =
    PRel of int
  | PCstr of peconstructor * pat list
  | PInac of constr
  | PHide of int

(** Substitutions: src_ctx ⊢ map_inst : tgt_ctx *)
type context_map = {
  src_ctx : rel_context;
  map_inst : pat list;
  tgt_ctx : rel_context;
}

(** Tag with a Constant.t application (needs env to infer type) *)
val mkInac : env -> esigma -> constr -> constr
val mkHide : env -> esigma -> constr -> constr

(* Constr of a pattern *)
val pat_constr : pat -> constr
val eq_pat : env -> Evd.evar_map -> pat -> pat -> bool

(* Constr of a pattern optionally marking innaccessibles and hidden patterns
   and modifying the evar_map in this case only. *)
val constr_of_pat : ?inacc_and_hide:bool -> env -> Evd.evar_map -> pat -> Evd.evar_map * constr
val constrs_of_pats : ?inacc_and_hide:bool -> env -> Evd.evar_map -> pat list -> Evd.evar_map * constr list

(** Free pattern variables (excluding inaccessibles and hiddens) *)
val pat_vars : pat -> Int.Set.t
val pats_vars : pat list -> Int.Set.t

(** Make the terms inaccessible *)
val inaccs_of_constrs : constr list -> pat list

(** Reverse of constr_of_pat turning applications of innac/hide into
    the proper patterns *)
val pats_of_constrs : Environ.env -> Evd.evar_map -> constr list -> pat list
val pat_of_constr : Environ.env -> Evd.evar_map -> constr -> pat

(** Translating back to user patterns. When [keep_names] is set, variable
    patterns reuse the context binder names verbatim (with [Implicit]
    provenance) instead of going through name generation, so that names of
    pre-existing hypotheses survive [Mangle Names]. *)
val context_map_to_lhs : ?avoid:Id.Set.t -> ?keep_names:bool -> ?loc:Loc.t -> context_map -> Syntax.lhs

(** Pretty-printing *)
val pr_constr_pat : env -> Evd.evar_map -> constr -> Pp.t
val pr_pat : env -> Evd.evar_map -> pat -> Pp.t
val pr_pats : env -> Evd.evar_map -> pat list -> Pp.t
val pr_context : env -> Evd.evar_map -> rel_context -> Pp.t
val ppcontext : rel_context -> unit
val pr_context_map : env -> Evd.evar_map -> context_map -> Pp.t
val ppcontext_map : env -> Evd.evar_map -> context_map -> unit
val ppcontext_map_empty : context_map -> unit
val pr_rel_name : env -> int -> Pp.t

(** Rename de Bruijn variables with fresh, distinct names *)
val do_renamings : env -> Evd.evar_map -> rel_context -> rel_context

val typecheck_map :
  Environ.env -> Evd.evar_map -> context_map -> unit
val check_ctx_map :
  ?unsafe:bool -> Environ.env -> Evd.evar_map -> context_map -> context_map

(** Smart constructor (doing runtime checks) *)
val mk_ctx_map : ?unsafe:bool -> Environ.env ->
  Evd.evar_map ->
  rel_context ->
  pat list ->
  rel_context -> context_map

val map_ctx_map :
  (EConstr.t -> EConstr.t) -> context_map -> context_map

val map_rel_ctx_map :
  (Evd.erelevance -> Evd.erelevance) -> context_map -> context_map

(** Substitution and specialization *)
val subst_pats_constr : Evd.evar_map -> int -> pat list -> constr -> constr
val subst_context : Evd.evar_map -> pat list -> rel_context -> rel_context
val specialize : Evd.evar_map -> pat list -> pat -> pat
val specialize_constr : Evd.evar_map -> pat list -> constr -> constr
val specialize_pats : Evd.evar_map -> pat list -> pat list -> pat list
val specialize_rel_context :
  Evd.evar_map -> pat list -> rel_context -> rel_context
val mapping_constr : Evd.evar_map -> context_map -> constr -> constr
val subst_constr_pat : Evd.evar_map -> int -> constr -> pat -> pat
val subst_constr_pats : Evd.evar_map -> int -> constr -> pat list -> pat list
val lift_patn : int -> int -> pat -> pat
val lift_patns : int -> int -> pat list -> pat list
val lift_pat : int -> pat -> pat
val lift_pats : int -> pat list -> pat list
val make_permutation : ?env:Environ.env -> Evd.evar_map ->
  context_map -> context_map -> context_map

val specialize_mapping_constr : Evd.evar_map -> context_map -> constr -> constr
val rels_of_ctx : ?with_lets:bool -> ('a,'b,'c) Context.Rel.pt -> constr list

val patvars_of_ctx : ?with_lets:bool -> ('a,'b,'c) Context.Rel.pt -> pat list
(** Includes lets by default *)

val pat_vars_list : int -> pat list
val intset_of_list : Int.Set.elt list -> Int.Set.t
val split_context : int -> 'a list -> 'a list * 'a * 'a list
val split_tele :
  int ->
  rel_context ->
  rel_context * rel_declaration *
    rel_context
val rels_above : 'a list -> int -> Int.Set.t
val is_fix_proto : Environ.env -> Evd.evar_map -> constr -> bool
val fix_rels : Environ.env -> Evd.evar_map -> rel_context -> Int.Set.t
val dependencies_of_rel :
  with_red:bool ->
  env ->
  Evd.evar_map ->
  rel_context ->
  Int.Set.elt ->
  Int.Set.elt -> Int.Set.t
val dependencies_of_term :
  with_red:bool ->
  env ->
  Evd.evar_map ->
  rel_context ->
  constr ->
  Int.Set.elt -> Int.Set.t
val non_dependent : Evd.evar_map ->
  ('a * 'b * constr) list -> constr -> Int.Set.t
val subst_term_in_context : Evd.evar_map ->
  constr -> rel_context -> rel_context
val strengthen :
  ?full:bool ->
  ?abstract:bool ->
  env ->
  Evd.evar_map ->
  rel_context ->
  Int.Set.elt ->
  constr ->
  context_map * context_map

(* Return a substitution and its inverse. *)
(* For more flexibility, [rels] is a set of indices which are to be
 * moved before the variable. By default, this is everything already before
 * the variable. *)
val new_strengthen :
  Environ.env -> Evd.evar_map ->
  rel_context -> int -> ?rels:Int.Set.t -> constr ->
  context_map * context_map

val id_pats : ('a, 'b,'c) Context.Rel.pt -> pat list
val id_subst : rel_context -> context_map
val eq_context_nolet :
  env ->
  Evd.evar_map -> rel_context -> rel_context -> bool
val check_eq_context_nolet :
  env ->
  Evd.evar_map ->
  context_map ->
  context_map -> unit
val compose_subst : ?unsafe:bool -> Environ.env ->
  ?sigma:Evd.evar_map ->
  context_map ->
  context_map ->
  context_map
val push_mapping_context : Evd.evar_map ->
  rel_declaration ->
  context_map ->
  context_map
val lift_subst :
  Environ.env -> Evd.evar_map -> context_map -> rel_context -> context_map
val single_subst :
  ?unsafe:bool ->
  env ->
  Evd.evar_map ->
  Int.Set.elt ->
  pat ->
  rel_context -> context_map

val filter_def_pats : context_map -> pat list
