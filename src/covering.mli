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
open Syntax
open Context_map
open Splitting

(* Unification *)

exception Conflict
exception Stuck
type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
type unification_result = (context_map * int * constr * pat) option

val unify :
  env ->
  Evd.evar_map ->
  Int.Set.t ->
  rel_context ->
  constr ->
  constr -> context_map
val unify_constrs :
  env ->
  Evd.evar_map ->
  Int.Set.t ->
  rel_context ->
  constr list ->
  constr list -> context_map
val flexible : pat list -> ('a,'b,'c) Context.Rel.pt -> Int.Set.t
val accessible : pat -> Int.Set.t
val accessibles : pat list -> Int.Set.t
val hidden : pat -> bool

type match_subst =
  ((Loc.t option * identifier * provenance) * pat) list * (Glob_term.glob_constr * pat) list *
  (user_pat_loc * constr) list * ((Loc.t option * pat) list)

val match_pattern : Environ.env -> Evd.evar_map -> user_pat_loc -> pat -> match_subst
val match_patterns : Environ.env -> Evd.evar_map -> user_pats -> pat list -> match_subst
val matches : Environ.env -> Evd.evar_map -> user_pats -> context_map -> match_subst unif_result
val match_user_pattern :
  Environ.env -> 
  pat -> user_pat_loc -> (int * user_pat) list * (identifier * pat) list
val match_user_patterns :
  Environ.env -> 
  pat list ->
  user_pats -> (int * user_pat) list * (identifier * pat) list
val matches_user :
  Environ.env -> 
  context_map ->
  user_pats ->
  ((int * user_pat) list * (identifier * pat) list) unif_result
val lets_of_ctx :
  env ->
  rel_context ->
  Evd.evar_map ref ->
  (Id.t * pat) list ->
  constr list *
  rel_context *
  rel_context


type int_data = {
  rec_type : rec_type;
  fixdecls : rel_context;
  flags : flags;
  program_mode : bool;
  intenv : Constrintern.internalization_env;
  notations : Vernacexpr.notation_declaration list
}

val add_wfrec_implicits : Syntax.rec_type ->
           Glob_term.glob_constr -> Glob_term.glob_constr

val interp_program_body : Environ.env ->
  Evd.evar_map -> EConstr.rel_context ->
  int_data ->
  Syntax.program_body ->
  EConstr.types option -> Evd.evar_map * EConstr.constr

val interp_constr_in_rhs_env : Environ.env ->
  Evd.evar_map ref ->
  int_data ->
  EConstr.rel_context * Environ.env * int * EConstr.Vars.substl ->
  int ->
  Syntax.program_body ->
  EConstr.t option ->
  EConstr.constr * EConstr.types

val interp_constr_in_rhs :
  env ->
  rel_context ->
  Evd.evar_map ref ->
  int_data ->
  constr option ->
  (Id.t * pat) list ->
  rel_context ->
  program_body -> constr * types

val unify_type :
  env ->
  Evd.evar_map ref ->
  rel_context ->
  'a ->
  types ->
  rel_context ->
  (constr *
   ((context_map) * int *
    constr * pat)
   unif_result array)
  option

val blockers : Environ.env -> user_pats -> context_map -> int list

val subst_matches_constr : Evd.evar_map ->
  int -> (int * constr) list -> constr -> constr
val is_all_variables : 'a * pat list * 'b -> bool

type 'a split_var_result =
  | Splitted of 'a
  | CannotSplit of Names.Name.t * rel_context * constr

val split_var :
  env * Evd.evar_map ref ->
  int ->
  rel_context ->
  (int * rel_context * context_map option array) split_var_result option
    
val find_empty : env * Evd.evar_map ref -> rel_context -> (int * rel_context * splitting option array) option
val variables_of_pats : pat list -> (int * bool) list
val pats_of_variables : (int * bool) list -> pat list
val lift_rel_declaration :
  int -> rel_declaration -> rel_declaration
val lookup_named_i :
  Id.t -> named_context -> int * named_declaration
val instance_of_pats : 
  Environ.env -> 
  Evd.evar_map ->
  rel_context ->
  (int * bool) list ->
  rel_context * pat list *
  pat list
val push_rel_context_eos : rel_context -> env -> esigma -> env
val split_at_eos : Environ.env -> Evd.evar_map ->
  named_context -> named_context * named_context
val pr_problem :
  program_info ->
  env -> Evd.evar_map -> context_map -> Pp.t
val rel_id : (Name.t * 'a * 'b) list -> int -> Id.t

val refine_arg : int -> rel_context -> int * int

val env_of_rhs :
           Evd.evar_map ref ->
           rel_context ->
           Environ.env ->
           (Names.Id.t * pat) list ->
           rel_declaration list ->
           rel_context *
           Environ.env * int * constr list

(** Covering computation *)

val covering_aux :
  env ->
  Evd.evar_map ref ->
  program_info -> int_data ->
  (pre_clause * (int * int)) list ->
  (pre_clause * (int * int)) list ->
  path ->
  context_map ->
  user_pats ->
  rel_context -> constr ->
  ((pre_clause * (int * int)) list * splitting) option

val covering :  ?check_unused:bool ->
  env ->
  Evd.evar_map ref ->
  program_info -> int_data ->
  pre_clause list -> path ->
  context_map -> user_pats ->
  constr -> splitting

val adjust_sign_arity : Environ.env ->
  Evd.evar_map -> program_info -> Syntax.pre_clause list ->
  Evd.evar_map * program_info

val compute_rec_type : rec_type -> program_info list -> rec_type
val print_program_info : env -> Evd.evar_map -> program_info list -> unit
val compute_fixdecls_data :
           Environ.env ->
           Evd.evar_map ref ->
           ?data:Constrintern.internalization_env ->
           Syntax.program_info list ->
           Constrintern.internalization_env *
           Equations_common.rel_declaration list * (ERelevance.t * EConstr.t) list

val wf_fix_constr :
  Environ.env ->
  Evd.evar_map ref ->
  EConstr.rel_context ->
  EConstr.t ->
  Sorts.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t * EConstr.t * EConstr.t

val wf_fix :
  Environ.env ->
  Evd.evar_map ref ->
  Vars.substl ->
  EConstr.rel_context ->
  EConstr.t ->
  Sorts.t ->
  Constrexpr.constr_expr ->
  Constrexpr.constr_expr option ->
  EConstr.t (* term *) * EConstr.t (* rel *) *
  (EConstr.t (* functional type *) *
   EConstr.t (* full functional type *) *
   EConstr.t (* fixpoint combinator *))

val compute_rec_data :
  Environ.env ->
  Evd.evar_map ref ->
  int_data ->
  Equations_common.rel_declaration list ->
  EConstr.Vars.substl ->
  Syntax.program_info ->
  Syntax.program_info * Context_map.context_map * EConstr.constr *
  (Syntax.user_pat, 'a) DAst.t list * Splitting.rec_info option


val interp_arity : Environ.env ->
  Evd.evar_map ref ->
  poly:PolyFlags.t ->
  is_rec:bool ->
  with_evars:bool ->
  Vernacexpr.notation_declaration list ->
  pre_equation Syntax.where_clause ->
  program_info

val coverings :
  Environ.env ->
  Evd.evar_map ref ->
  int_data ->
  Syntax.program_info list ->
  pre_equation list list ->
  Splitting.program list
