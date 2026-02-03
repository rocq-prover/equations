(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open EConstr
open Environ
open Names
open Ltac_plugin

type 'a peuniverses = 'a * EConstr.EInstance.t

(* Options *)
val simplify_withUIP : bool ref
val equations_with_funext : bool ref
val equations_transparent : bool ref
val equations_derive_equations : bool ref
val equations_derive_eliminator : bool ref
val equations_obligations : unit -> bool

val get_debug : unit -> bool
val debug : (unit -> Pp.t) -> unit
val equations_debug : (unit -> Pp.t) -> unit

val equations_category : CWarnings.category

val ppenv_sigma : (Environ.env -> Evd.evar_map -> 'a -> Pp.t) -> 'a -> unit

val enter_goal : (Environ.env -> Evd.evar_map -> EConstr.t -> unit Proofview.tactic) -> unit Proofview.tactic

(* Common flags *)
type flags = {
  poly : PolyFlags.t;
  (** Whether to use universe polymorphic or monomorphic definitions. *)

  obligations : bool;
  (** Create obligations for unsolved goals. *)

  open_proof : bool;
  (** Use interactive proof mode instead of obligations for unsolved goals. *)

  with_eqns : bool;
  (** Generate equations corresponding to the clauses. *)

  with_ind : bool;
  (** Generate the inductive graph and derived eliminator.
      Implies [with_eqns]. *)

  allow_aliases : bool;
  (** Allow two occurrences of a variable to be unified with different
      values (one shadows the other). *)

  tactic : unit Proofview.tactic;
  (** The default tactic to try to solve obligations/holes. *)
}

(* Point-free composition *)
val ( $ ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val ( &&& ) : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd

val id : 'a -> 'a

val array_remove_last : 'a array -> 'a array
val array_chop_last : 'a array -> 'a array * 'a array
val rev_assoc : ('a -> 'b -> bool) -> 'a -> ('c * 'b) list -> 'c
val array_filter_map : ('a -> 'b option) -> 'a array -> 'b array

(* All the tails of [x1 ... xn] : [[xn]; [xn-1; xn] ...[x2 .. xn]] *)
val proper_tails : 'a list -> 'a list list

(* Stop at the first Some *)
val list_find_map_i : (int -> 'a -> 'b option) -> int -> 'a list -> 'b option

type esigma = Evd.evar_map ref

val head_of_constr : Evd.evar_map -> constr -> constr
val nowhere : 'a Locus.clause_expr
val dummy_loc : Loc.t option
type 'a located = 'a Loc.located

(** Fresh names *)
val fresh_id_in_env :
  ?avoid:Names.Id.Set.t -> Names.Id.t -> Environ.env -> Names.Id.t

(** Refer to a tactic *)
val tac_of_string :
  string ->
  Tacexpr.r_dispatch Tacexpr.gen_tactic_arg list -> unit Proofview.tactic

type rel_context = EConstr.rel_context
type rel_declaration = EConstr.rel_declaration
type named_declaration = EConstr.named_declaration
type named_context = EConstr.named_context
       
(** Context lifting *)
val lift_rel_contextn :
  int -> int -> rel_context -> rel_context

val lift_rel_context : int -> rel_context -> rel_context

val lift_list : constr list -> constr list
val lift_constrs : int -> constr list -> constr list

(** Checking *)
val check_term :
  Environ.env -> Evd.evar_map -> constr -> types -> unit
val check_type : Environ.env -> Evd.evar_map -> types -> unit
val typecheck_rel_context :
  Environ.env -> Evd.evar_map -> rel_context -> unit

val e_conv :
  env -> esigma -> constr -> constr -> bool

val e_type_of : env -> esigma -> constr -> types
						     
(** Term manipulation *)

val mkProd_or_subst :
  rel_declaration ->
  types -> types
val mkProd_or_clear : Evd.evar_map -> rel_declaration -> constr -> constr
val it_mkProd_or_clear : Evd.evar_map -> 
  constr -> rel_declaration list -> constr
val mkLambda_or_subst :
  rel_declaration ->
  constr -> constr
val mkLambda_or_subst_or_clear : Evd.evar_map -> rel_declaration ->
                                 constr -> constr
val mkProd_or_subst_or_clear : Evd.evar_map -> rel_declaration ->
                               constr -> types
val it_mkProd_or_subst : Environ.env -> Evd.evar_map -> types -> rel_declaration list -> constr
val it_mkProd_or_clean : Environ.env -> Evd.evar_map -> constr -> rel_context -> constr
val it_mkLambda_or_subst :
  Environ.env -> constr -> rel_declaration list -> constr
val it_mkLambda_or_subst_or_clear : Evd.evar_map -> constr -> rel_context -> constr
val it_mkProd_or_subst_or_clear : Evd.evar_map -> constr -> rel_context -> constr
val it_mkLambda_or_clear_LetIn : Evd.evar_map -> constr -> rel_context -> constr

val ids_of_constr : Evd.evar_map ->
  ?all:bool -> Id.Set.t -> constr -> Id.Set.t
val deps_of_var : Evd.evar_map -> Id.t -> env -> Id.Set.t
val idset_of_list : Id.t list -> Id.Set.t

val decompose_indapp : Evd.evar_map ->
  constr -> constr array -> constr * constr array

val refresh_universes_strict : Environ.env -> esigma -> types -> types

val new_global : Evd.evar_map -> Names.GlobRef.t -> Evd.evar_map * constr
val e_new_global : esigma -> Names.GlobRef.t -> constr
                                                                 
(** {6 Linking to Coq} *)

val global_reference : Id.t -> Names.GlobRef.t

val get_class : Evd.evar_map -> constr -> Typeclasses.typeclass * EConstr.EInstance.t

val make_definition :
  ?opaque:'a ->
  ?poly:PolyFlags.t ->
  Evd.evar_map ->
  ?types:constr -> constr -> Evd.evar_map * Declare.proof_entry

(** Declares a constant relative to an evar_map.

    It returns a constant and, in addition, an evar_map and econstr
   corresponding to it.

   - If the constant is polymorphic, it returns the
     minimized universes and a well-formed instance of the constant in that evar_map.
   - If it is not polymorphic, it returns a fresh evar map from the updated global
     environment.

   This allows easy construction of tactics that generate multiple related constants,
   even in the polymorphic case. *)

val declare_constant :
  ?check:bool ->
  Id.t ->
  constr ->
  constr option ->
  poly:PolyFlags.t ->
  kind:Decls.logical_kind ->
  Evd.evar_map ->
  Constant.t * (Evd.evar_map * EConstr.t)

val declare_mutual :
  poly:PolyFlags.t ->
  'a Syntax.mutual_fix ->
  Evd.evar_map ->
  Evd.evar_map * (Syntax.program_info * 'a * EConstr.t) list

val declare_instance :
  Names.Id.t ->
  poly:PolyFlags.t ->
  Evd.evar_map ->
  rel_context ->
  Typeclasses.typeclass peuniverses -> constr list -> Constant.t * (Evd.evar_map * EConstr.t)

(** Standard datatypes *)

type lazy_ref = Names.GlobRef.t Lazy.t

val equations_lib_ref : string -> Names.GlobRef.t
val find_global : string -> lazy_ref

val logic_sort : UnivGen.QualityOrSet.t lazy_t
val logic_eq_type : lazy_ref
val logic_eq_refl : lazy_ref
val logic_eq_case : lazy_ref
val logic_eq_elim : lazy_ref

(** In Prop, True is top, bot is False, conjunction is and *)
val logic_top : lazy_ref
val logic_top_intro : lazy_ref
val logic_top_elim : lazy_ref

val logic_bot : lazy_ref
val logic_bot_case : lazy_ref
val logic_bot_elim : lazy_ref

val logic_conj : lazy_ref
val logic_conj_intro : lazy_ref

val logic_unit : lazy_ref
val logic_unit_intro : lazy_ref

val logic_product : lazy_ref
val logic_pair : lazy_ref

val logic_relation : lazy_ref
val logic_wellfounded : lazy_ref
val logic_wellfounded_class : lazy_ref
val logic_transitive_closure : lazy_ref

val logic_eqdec_class : lazy_ref
val logic_eqdec_dec_eq : lazy_ref
val logic_uip_class : lazy_ref
val logic_uip_uip : lazy_ref

val logic_signature_class : lazy_ref
val logic_signature_sig : lazy_ref
val logic_signature_pack : lazy_ref

val get_fresh : Evd.evar_map -> lazy_ref -> Evd.evar_map * constr
val get_efresh : lazy_ref -> esigma -> constr
val is_lglobal : Environ.env -> Evd.evar_map -> lazy_ref -> EConstr.constr -> bool

val coq_sigma : lazy_ref
val coq_sigmaI : lazy_ref
val coq_pr1 : Names.Projection.t lazy_t
val coq_pr2 : Names.Projection.t lazy_t

val logic_tele_type : lazy_ref
val logic_tele_tip : lazy_ref
val logic_tele_ext : lazy_ref
val logic_tele_interp : lazy_ref
val logic_tele_measure : lazy_ref
val logic_tele_fix : lazy_ref
val logic_tele_fix_functional_type : lazy_ref
val logic_tele_fix_unfold : lazy_ref
val logic_tele_MR : lazy_ref

(** Constants used in the telescopic fixpoint, to be unfolded agressively *)
val logic_tele_type_app : lazy_ref
val logic_tele_forall_type_app : lazy_ref
val logic_tele_forall_uncurry : lazy_ref
val logic_tele_forall : lazy_ref
val logic_tele_forall_pack : lazy_ref
val logic_tele_forall_unpack : lazy_ref


val coq_zero : lazy_ref
val coq_succ : lazy_ref
val coq_nat : lazy_ref
val coq_nat_of_int : Evd.evar_map -> int -> Evd.evar_map * EConstr.t
val int_of_coq_nat : Constr.t -> int

val coq_fix_proto : lazy_ref

val fresh_sort_in_quality_or_set : esigma -> UnivGen.QualityOrSet.t -> constr
val fresh_logic_sort : esigma -> constr
val mkapp : Environ.env -> esigma -> lazy_ref -> constr array -> constr

val mkEq : Environ.env ->
  esigma -> types -> constr -> constr -> constr
val mkRefl : Environ.env -> esigma -> ?inst:EConstr.EInstance.t -> types -> constr -> constr

(** Bindings to theories/ files *)

val subterm_relation_base : string

val functional_induction_class :
  Evd.evar_map -> Evd.evar_map * Typeclasses.typeclass peuniverses
val functional_elimination_class :
  Evd.evar_map -> Evd.evar_map * Typeclasses.typeclass peuniverses
val dependent_elimination_class :
  esigma -> Typeclasses.typeclass peuniverses

val coq_noconfusion_class : Names.GlobRef.t lazy_t
val coq_nocycle_class : Names.GlobRef.t lazy_t
val coq_bang : Names.GlobRef.t Lazy.t
val coq_inacc : Names.GlobRef.t Lazy.t
val coq_block : Names.GlobRef.t Lazy.t
val coq_hide : Names.GlobRef.t Lazy.t
val coq_hidebody : Names.GlobRef.t Lazy.t
val coq_add_pattern : Names.GlobRef.t Lazy.t
val coq_end_of_section_id : Names.Id.t
val coq_the_end_of_the_section : Names.GlobRef.t Lazy.t
val coq_end_of_section : Names.GlobRef.t Lazy.t
val coq_ImpossibleCall : esigma -> constr
val unfold_add_pattern : unit Proofview.tactic lazy_t

val observe : string -> unit Proofview.tactic -> unit Proofview.tactic
  
val unfold_recursor_tac : unit -> unit Proofview.tactic
val unfold_recursor_ext_tac : unit -> unit Proofview.tactic
val equations_tac : unit -> unit Proofview.tactic
val set_eos_tac : unit -> unit Proofview.tactic
val solve_rec_tac : unit -> unit Proofview.tactic
val find_empty_tac : unit -> unit Proofview.tactic
val solve_subterm_tac : unit -> unit Proofview.tactic
val pi_tac : unit -> unit Proofview.tactic
val noconf_tac : unit -> unit Proofview.tactic
val noconf_hom_tac : unit -> unit Proofview.tactic
val eqdec_tac : unit -> unit Proofview.tactic
val simpl_equations_tac : unit -> unit Proofview.tactic
val solve_equation_tac : Names.GlobRef.t -> unit Proofview.tactic
val impossible_call_tac : Names.GlobRef.t -> Genarg.glevel Genarg.generic_argument
val depelim_tac : Names.Id.t -> unit Proofview.tactic
val do_empty_tac : Names.Id.t -> unit Proofview.tactic
val depelim_nosimpl_tac : Names.Id.t -> unit Proofview.tactic
val simpl_dep_elim_tac : unit -> unit Proofview.tactic
val depind_tac : Names.Id.t -> unit Proofview.tactic
val rec_wf_tac :            Genredexpr.r_trm -> Genredexpr.r_trm ->
           Names.Id.t -> Genredexpr.r_trm ->
                         Tacexpr.r_dispatch Tacexpr.gen_tactic_expr

(** [autounfold_first db db' loc gl] 
  Unfolds the two first occurrences in respectively t and t' of 
  Constant.t's declared unfoldable in db and db'
  (with Hint Unfold) if the goal is of the shape (@eq _ t t'), or fail. *)
val autounfold_heads :
  Hints.hint_db_name list ->
  Hints.hint_db_name list ->
  Locus.hyp_location option ->
  unit Proofview.tactic
val specialize_mutfix_tac : unit -> unit Proofview.tactic

type hintdb_name = string
val db_of_constr : Constr.t -> hintdb_name
val dbs_of_constrs : Constr.t list -> hintdb_name list

val pr_smart_global :
  Libnames.qualid Constrexpr.or_by_notation -> Pp.t
val string_of_smart_global :
  Libnames.qualid Constrexpr.or_by_notation -> string
val ident_of_smart_global :
  Libnames.qualid Constrexpr.or_by_notation -> Id.t

val move_after_deps : Names.Id.t -> constr -> unit Proofview.tactic
val assert_replacing : Names.Id.t -> constr -> types -> unit Proofview.tactic

val extended_rel_vect : int -> rel_context -> constr array
val extended_rel_list : int -> rel_context -> constr list
val to_tuple : rel_declaration -> Names.Name.t binder_annot * constr option * constr
val to_named_tuple : named_declaration -> Names.Id.t binder_annot * constr option * constr
val of_tuple : Names.Name.t binder_annot * constr option * constr -> rel_declaration
val of_named_tuple : Names.Id.t binder_annot * constr option * constr -> named_declaration

val get_type : rel_declaration -> constr
val get_name : rel_declaration -> Names.Name.t
val get_annot : rel_declaration -> Names.Name.t binder_annot
val get_value : rel_declaration -> constr option
val make_assum : Names.Name.t binder_annot -> constr -> rel_declaration
val make_def : Names.Name.t binder_annot -> constr option -> constr -> rel_declaration
val make_named_def : Names.Id.t binder_annot -> constr option -> constr -> named_declaration
val to_context : (Names.Name.t binder_annot * constr option * constr) list -> rel_context

val named_of_rel_context : ?keeplets:bool -> (unit -> Names.Id.t) -> rel_context -> EConstr.t list * constr list * named_context
val rel_of_named_context : Evd.evar_map -> named_context -> rel_context * Names.Id.t list
val subst_rel_context : int -> EConstr.t list -> rel_context -> rel_context
val get_id : named_declaration -> Names.Id.t
val get_named_type : named_declaration -> constr
val get_named_value : named_declaration -> constr option

val lookup_rel : int -> rel_context -> rel_declaration
val fold_named_context_reverse : ('a -> named_declaration -> 'a) -> init:'a -> named_context -> 'a
val map_rel_context : (constr -> constr) -> rel_context -> rel_context
val map_rel_relevance : (Evd.erelevance -> Evd.erelevance) -> rel_context -> rel_context
val map_rel_declaration : (constr -> constr) -> rel_declaration -> rel_declaration
val map_named_declaration : (constr -> constr) -> named_declaration -> named_declaration
val map_named_context : (constr -> constr) -> named_context -> named_context
val lookup_named : Id.t -> named_context -> named_declaration

val to_evar_map : Evd.evar_map -> Evd.evar_map
val of_evar_map : Evd.evar_map -> Evd.evar_map

val pp : Pp.t -> unit
val user_err_loc : (Loc.t option * Pp.t) -> 'a
val error : string -> 'a
val errorlabstrm : Pp.t -> 'a
val print_error : exn -> Pp.t
val anomaly : ?label:string -> Pp.t -> 'a
                                
val nf_betadeltaiota : Reductionops.reduction_function

val subst_telescope : constr -> rel_context -> rel_context
val subst_in_ctx : int -> constr -> rel_context -> rel_context
val set_in_ctx : int -> constr -> rel_context -> rel_context
val subst_in_named_ctx :
  Evd.evar_map -> Names.Id.t -> constr -> named_context -> named_context

val new_evar :            Environ.env ->
           Evd.evar_map ->
           ?src:Evar_kinds.t Loc.located ->
           types -> Evd.evar_map * constr

val new_type_evar :            Environ.env ->
           Evd.evar_map -> 
           ?src:Evar_kinds.t Loc.located -> Evd.rigid ->
           Evd.evar_map * (constr * ESorts.t)

val empty_hint_info : 'a Typeclasses.hint_info_gen

val evar_absorb_arguments :
  Environ.env -> Evd.evar_map ->
  existential ->
  constr list -> Evd.evar_map * existential


val hintdb_set_transparency :
  Constant.t -> bool -> Hints.hint_db_name -> unit
  
(** To add to the API *)
val to_peuniverses : 'a UVars.puniverses -> 'a peuniverses
val from_peuniverses : Evd.evar_map -> 'a peuniverses -> 'a UVars.puniverses

val is_global : Environ.env -> Evd.evar_map -> Names.GlobRef.t -> constr -> bool
val constr_of_global_univ : Evd.evar_map -> Names.GlobRef.t peuniverses -> constr

val rel_vect : int -> int -> constr array
val applistc : constr -> constr list -> constr

val instance_constructor : Evd.evar_map -> Typeclasses.typeclass peuniverses -> constr list ->
  constr option * types
val decompose_appvect : Evd.evar_map -> constr -> constr * constr array

val dest_ind_family : Inductiveops.inductive_family -> inductive peuniverses * constr list
val prod_appvect : Evd.evar_map -> constr -> constr array -> constr
val beta_appvect : Evd.evar_map -> constr -> constr array -> constr

val find_rectype : Environ.env -> Evd.evar_map -> types -> Inductiveops.inductive_family * constr list

type identifier = Names.Id.t

val evd_comb1 : (Evd.evar_map -> 'a -> Evd.evar_map * 'b) -> Evd.evar_map ref -> 'a -> 'b
val evd_comb0 : (Evd.evar_map -> Evd.evar_map * 'b) -> Evd.evar_map ref -> 'b

val splay_prod_n_assum : env -> Evd.evar_map -> int -> types -> rel_context * types

(* Universes *)
val nonalgebraic_universe_level_of_universe :
  Environ.env -> Evd.evar_map -> ESorts.t -> Evd.evar_map * Univ.Universe.t * ESorts.t
val instance_of :
  Environ.env ->
  Evd.evar_map ->
  ?argu:EConstr.EInstance.t ->
  ESorts.t ->
  Evd.evar_map * EConstr.EInstance.t * ESorts.t

val collapse_term_qualities : UState.t -> Constr.t -> Constr.t
(* Hack to prevent sending terms with unbound qualities to the kernel *)
