open Pp
open EConstr
open Equations_common

(* ========== Coq references ========= *)
(* This section should change a lot when we approach an actual solution. *)

module type SIGMAREFS = sig
  val sigma : Names.inductive Lazy.t
  val sigmaI : Names.constructor Lazy.t
end

module type EQREFS = sig
  (* Equality type. *)
  val eq : Names.inductive Lazy.t
  val eq_refl : Names.constructor Lazy.t
  (* Decidable equality typeclass. *)
  val uip : Names.Constant.t Lazy.t
  (* Logic types. *)
  val zero : Names.inductive Lazy.t
  val one : Names.inductive Lazy.t
  val one_val : Names.constructor Lazy.t
  val one_ind_dep : Names.Constant.t Lazy.t
  val zero_ind : Names.Constant.t Lazy.t
  val zero_ind_dep : Names.Constant.t Lazy.t
  (* NoConfusion. *)
  val noConfusion : Names.inductive Lazy.t
  val apply_noConfusion : Names.Constant.t Lazy.t
  (* NoCycle *)
  val noCycle : Names.inductive Lazy.t
  val apply_noCycle_left : Names.Constant.t Lazy.t
  val apply_noCycle_right : Names.Constant.t Lazy.t

  val simplify_ind_pack : Names.Constant.t Lazy.t
  val simplify_ind_pack_inv : Names.Constant.t Lazy.t
  val opaque_ind_pack_eq_inv : Names.Constant.t Lazy.t
  (* Simplification of dependent pairs. *)
  val simpl_sigma : Names.Constant.t Lazy.t
  val simpl_sigma_dep : Names.Constant.t Lazy.t
  val simpl_sigma_nondep_dep : Names.Constant.t Lazy.t
  val simpl_sigma_dep_dep : Names.Constant.t Lazy.t
  val pack_sigma_eq : Names.Constant.t Lazy.t
  (* Deletion using UIP. *)
  val simpl_uip : Names.Constant.t Lazy.t
  (* Solution lemmas. *)
  val solution_left : Names.Constant.t Lazy.t
  val solution_left_dep : Names.Constant.t Lazy.t
  val solution_right : Names.Constant.t Lazy.t
  val solution_right_dep : Names.Constant.t Lazy.t
end

module RefsHelper = struct
  let init_gr s = Lazy.force s
  let init_inductive s = lazy (Globnames.destIndRef (init_gr s))
  let init_constructor s = lazy (Globnames.destConstructRef (init_gr s))
  let init_constant s = lazy (Globnames.destConstRef (init_gr s))
end

(* This should be parametrizable by the user. *)
module EqRefs : EQREFS = struct
  include RefsHelper

  open Equations_common

  let eq = init_inductive logic_eq_type
  let eq_refl = init_constructor logic_eq_refl
  let uip = init_constant logic_uip_class
  let zero = init_inductive logic_bot
  let one = init_inductive logic_top
  let one_val = init_constructor logic_top_intro
  let one_ind_dep = init_constant logic_top_elim
  let zero_ind = init_constant logic_bot_case
  let zero_ind_dep = init_constant logic_bot_elim

  let noConfusion = init_inductive coq_noconfusion_class
  let noCycle = init_inductive coq_nocycle_class

  let init_depelim s = init_constant (find_global ("depelim." ^ s))

  let apply_noConfusion = init_depelim "apply_noConfusion"
  let apply_noCycle_left = init_depelim "apply_noCycle_left"
  let apply_noCycle_right = init_depelim "apply_noCycle_right"
  let simplify_ind_pack = init_depelim "simplify_ind_pack"
  let simplify_ind_pack_inv = init_depelim "simplify_ind_pack_inv"
  let opaque_ind_pack_eq_inv = init_depelim "opaque_ind_pack_eq_inv"
  let simpl_sigma = init_depelim "simpl_sigma"
  let simpl_sigma_dep = init_depelim "simpl_sigma_dep"
  let simpl_sigma_nondep_dep = init_depelim "simpl_sigma_nondep_dep"
  let simpl_sigma_dep_dep = init_depelim "simpl_sigma_dep_dep"
  let pack_sigma_eq = init_depelim "pack_sigma_eq"
  let simpl_uip = init_depelim "simpl_uip"
  let solution_left = init_depelim "solution_left"
  let solution_left_dep = init_depelim "solution_left_dep"
  let solution_right = init_depelim "solution_right"
  let solution_right_dep = init_depelim "solution_right_dep"
end

(* This should not. *)
module SigmaRefs : SIGMAREFS = struct
  include RefsHelper

  let sigma = init_inductive Equations_common.coq_sigma
  let sigmaI = init_constructor Equations_common.coq_sigmaI
end

(* From the references, we can build terms. *)

type constr_gen = Evd.evar_map ref -> EConstr.constr

type constr_univ_gen = EConstr.EInstance.t -> EConstr.constr

module type BUILDER = sig
  val sigma : constr_gen
  val sigmaI : constr_gen
  val eq : constr_gen
  val equ : constr_univ_gen
  val eq_refl : constr_univ_gen
  val uip : constr_gen
  val zero : constr_gen
  val one : constr_gen
  val one_val : constr_gen
  val one_ind_dep : constr_univ_gen
  val zero_ind : constr_univ_gen
  val zero_ind_dep : constr_univ_gen
  val noConfusion : constr_gen
  val apply_noConfusion : constr_univ_gen
  val noCycle : constr_gen
  val apply_noCycle_left : constr_gen
  val apply_noCycle_right : constr_gen
  val simplify_ind_pack : constr_gen
  val simplify_ind_pack_inv : constr_gen
  val simpl_sigma : constr_gen
  val simpl_sigma_dep : constr_gen
  val simpl_sigma_nondep_dep : constr_gen
  val simpl_sigma_dep_dep : constr_gen
  val simpl_uip : constr_gen
  val solution_left : constr_univ_gen
  val solution_left_dep : constr_univ_gen
  val solution_right : constr_univ_gen
  val solution_right_dep : constr_univ_gen
end

module BuilderHelper = struct
  let gen_from_inductive ind = fun evd ->
    let glob = Names.GlobRef.IndRef (Lazy.force ind) in
    Equations_common.e_new_global evd glob
  let gen_from_inductive_univ ind u =
    let glob = Names.GlobRef.IndRef (Lazy.force ind) in
    EConstr.mkRef (glob, u)
  let gen_from_constant cst = fun evd ->
    let glob = Names.GlobRef.ConstRef (Lazy.force cst) in
    Equations_common.e_new_global evd glob
  let gen_from_constant_univ cst u =
    let glob = Names.GlobRef.ConstRef (Lazy.force cst) in
    EConstr.mkRef (glob, u)
  let gen_from_constructor constr = fun evd ->
    let glob = Names.GlobRef.ConstructRef (Lazy.force constr) in
    Equations_common.e_new_global evd glob
  let gen_from_constructor_univ constr = fun u ->
    let glob = Names.GlobRef.ConstructRef (Lazy.force constr) in
    EConstr.mkRef (glob, u)
end

module BuilderGen (SigmaRefs : SIGMAREFS) (EqRefs : EQREFS) : BUILDER = struct
  include BuilderHelper

  let sigma = gen_from_inductive SigmaRefs.sigma
  let sigmaI = gen_from_constructor SigmaRefs.sigmaI
  let eq = gen_from_inductive EqRefs.eq
  let equ u = gen_from_inductive_univ EqRefs.eq u

  let eq_refl = gen_from_constructor_univ EqRefs.eq_refl
  let uip = gen_from_constant EqRefs.uip
  let zero = gen_from_inductive EqRefs.zero
  let one = gen_from_inductive EqRefs.one
  let one_val = gen_from_constructor EqRefs.one_val
  let one_ind_dep = gen_from_constant_univ EqRefs.one_ind_dep
  let zero_ind = gen_from_constant_univ EqRefs.zero_ind
  let zero_ind_dep = gen_from_constant_univ EqRefs.zero_ind_dep
  let noConfusion = gen_from_inductive EqRefs.noConfusion
  let apply_noConfusion = gen_from_constant_univ EqRefs.apply_noConfusion
  let noCycle = gen_from_inductive EqRefs.noCycle
  let apply_noCycle_left = gen_from_constant EqRefs.apply_noCycle_left
  let apply_noCycle_right = gen_from_constant EqRefs.apply_noCycle_right
  let simplify_ind_pack = gen_from_constant EqRefs.simplify_ind_pack
  let simplify_ind_pack_inv = gen_from_constant EqRefs.simplify_ind_pack_inv
  let simpl_sigma = gen_from_constant EqRefs.simpl_sigma
  let simpl_sigma_dep = gen_from_constant EqRefs.simpl_sigma_dep
  let simpl_sigma_nondep_dep = gen_from_constant EqRefs.simpl_sigma_nondep_dep
  let simpl_sigma_dep_dep = gen_from_constant EqRefs.simpl_sigma_dep_dep
  let simpl_uip = gen_from_constant EqRefs.simpl_uip
  let solution_left = gen_from_constant_univ EqRefs.solution_left
  let solution_left_dep = gen_from_constant_univ EqRefs.solution_left_dep
  let solution_right = gen_from_constant_univ EqRefs.solution_right
  let solution_right_dep = gen_from_constant_univ EqRefs.solution_right_dep
end

module Builder : BUILDER = BuilderGen(SigmaRefs)(EqRefs)

(* ========== Simplification ========== *)

(* Some types to define what is a simplification. *)
type direction = Left | Right

type simplification_step =
    Deletion of bool (* Force the use of K? *)
  | Solution of direction
  | NoConfusion of simplification_rules
  | NoConfusionOut (* Step for the inversion of [simplify_ind_pack]. *)
  | NoCycle (* TODO: NoCycle should probably take a direction too. *)
  | ElimTrue | ElimFalse
and simplification_rule =
    Step of simplification_step
  | Infer_one
  | Infer_direction
  | Infer_many
and simplification_rules = (Loc.t option * simplification_rule) list

type goal = rel_context * EConstr.types * ESorts.t
type open_term = (goal * EConstr.existential) option * EConstr.constr

type simplification_error =
| NotAProduct
| FirstHypNotAnEquality
| FirstHypNotAnEqualityIdentical
| FirstHypLHSNotVariable
| FirstHypRHSNotVariable
| DependentPair
| AnomalyReport
| UIPneeded of Environ.env * Evd.evar_map * types * bool
| VariableOnBothSides
| LetBoundVariable
| CannotRemoveDependency
| NotConstructorEquality
| UIPorNoConfusionneeded of Environ.env * Evd.evar_map * types * Names.inductive
| NoConfusionHomneeded of Environ.env * Evd.evar_map * types * Names.inductive
| NoConfusionneeded of Environ.env * Evd.evar_map * types
| NoCycleneeded of Environ.env * Evd.evar_map * types
| NoCycleCannotInfer of Environ.env * Evd.evar_map * types
| PackEqPartialApplication
| PackEqAnomaly
| FirstHypNotUnit
| FirstHypNotEmpty
| BothNotVariable
| CannotInferStep
| AProduct

let explain_simplification_error = function
| NotAProduct ->
  strbrk "The goal is not a product."
| FirstHypNotAnEquality ->
  strbrk "The first hypothesis in the goal is not an equality."
| FirstHypNotAnEqualityIdentical ->
  strbrk "The first hypothesis in the goal is not an equality between identical terms."
| FirstHypLHSNotVariable ->
  strbrk "The left-hand side of the first hypothesis in the goal is not a variable."
| FirstHypRHSNotVariable ->
  strbrk "The right-hand side of the first hypothesis in the goal is not a variable."
| DependentPair ->
  strbrk "Cannot simplify dependent pair."
| AnomalyReport ->
  strbrk "If you see this, please report."
| UIPneeded (env, sigma, t, uip) ->
  strbrk "[deletion] Cannot simplify without UIP on type " ++
  Printer.pr_econstr_env env sigma t ++
  (if not uip then strbrk " and the 'Equations With UIP' flag is off" else mt ())
| VariableOnBothSides ->
  strbrk "[solution] The variable appears on both sides of the equality."
| LetBoundVariable ->
  strbrk "[solution] cannot apply to a let-bound variable."
| CannotRemoveDependency ->
  strbrk "[solution] cannot remove dependency in the variable."
| NotConstructorEquality ->
  strbrk "This is not an equality between constructors."
| UIPorNoConfusionneeded (env, sigma, t, mind) ->
  strbrk "[noConfusion] Cannot simplify without UIP on type " ++
  Printer.pr_econstr_env env sigma t ++
  strbrk " or NoConfusion for family " ++ Printer.pr_inductive env mind
| NoConfusionHomneeded (env, sigma, t, mind) ->
  strbrk "[noConfusion] Trying to use a non-definitional noConfusion rule on " ++
  Printer.pr_econstr_env env sigma t ++
  strbrk ", which does not have a [NoConfusionHom] instance." ++ spc () ++
  strbrk "Either [Derive NoConfusionHom for " ++ Printer.pr_inductive env mind ++
  strbrk "], or [Derive NoConfusion for " ++ Printer.pr_inductive env mind ++
  strbrk "] if it requires uniqueness of identity proofs and" ++
  strbrk " enable [Equations With UIP] to allow this"
| NoConfusionneeded (env, sigma, t) ->
  strbrk "[noConfusion] Cannot find an instance of NoConfusion for type " ++
  Printer.pr_econstr_env env sigma t
| PackEqPartialApplication ->
  strbrk "Expected a full application of [opaque_ind_pack_eq_inv]. Maybe \
  you did not solve completely a NoConfusion step?"
| PackEqAnomaly ->
  strbrk "[opaque_ind_pack_eq_inv] Anomaly: should be applied to a reflexivity proof."
| NoCycleneeded (env, sigma, t) ->
  strbrk "[noConfusion] Cannot find an instance of NoCycle for type " ++
  Printer.pr_econstr_env env sigma t
| NoCycleCannotInfer (env, sigma, t) ->
  strbrk "[noCycle] Cannot infer a proof of " ++
  Printer.pr_econstr_env env sigma t
| FirstHypNotUnit ->
  strbrk "[elim_true] The first hypothesis is not the unit type."
| FirstHypNotEmpty ->
  strbrk "[elim_true] The first hypothesis is not the empty type."
| BothNotVariable ->
  strbrk "Neither side of the equality is a variable."
| CannotInferStep ->
  strbrk "Could not infer a simplification step."
| AProduct ->
  strbrk "a product"

exception CannotSimplify of simplification_error

let _ = CErrors.register_handler begin function
| CannotSimplify e -> Some (explain_simplification_error e)
| _ -> None
end

let check_context ~where ?name env evd ctx =
  let rec check env sigma ctx = match ctx with
  | [] -> env, sigma
  | decl :: ctx ->
    let env, sigma = check env sigma ctx in
    let open Context.Rel.Declaration in
    let sigma = match decl with
    | LocalAssum (na, t) ->
      let sigma, _ = Typing.sort_of env sigma t in
      sigma
    | LocalDef (na, c, t) ->
      let sigma, _ = Typing.sort_of env sigma t in
      Typing.check env sigma c t
    in
    push_rel decl env, sigma
  in
  let _env, sigma =
    try check env evd ctx
    with Type_errors.TypeError (env, tyerr) ->
      anomaly Pp.(str where ++ spc () ++
        str "Equations build an ill-typed context: " ++ Printer.pr_rel_context env evd (EConstr.Unsafe.to_rel_context ctx) ++
        Himsg.explain_pretype_error env evd
          (Pretype_errors.TypingError (Pretype_errors.of_type_error tyerr)))
    | Pretype_errors.PretypeError (env, evd, tyerr) ->
        anomaly Pp.(str where ++ spc () ++
        str "Equations build an ill-typed context: " ++ Printer.pr_rel_context env evd (EConstr.Unsafe.to_rel_context ctx) ++
        Himsg.explain_pretype_error env evd tyerr)
  in
  let check = Evd.check_poly_constraints evd (snd @@ Evd.sort_context_set sigma) in
  if not check then anomaly Pp.(str where ++ spc () ++ str "Equations missing constraints in " ++
    str (Option.default "(anonymous)" name))

(* Full type-checking + check that constraints are present *)
let check_typed ~where ?name env evd c =
  let sigma, _ =
    try Typing.type_of env evd c
    with Type_errors.TypeError (env, tyerr) ->
      anomaly Pp.(str where ++ spc () ++
        str "Equations build an ill-typed term: " ++ Printer.pr_econstr_env env evd c ++
        Himsg.explain_pretype_error env evd
          (Pretype_errors.TypingError (Pretype_errors.of_type_error tyerr)))
    | Pretype_errors.PretypeError (env, evd, tyerr) ->
        anomaly Pp.(str where ++ spc () ++
        str "Equations build an ill-typed term: " ++ Printer.pr_econstr_env env evd c ++
        Himsg.explain_pretype_error env evd tyerr)
  in
  let check = Evd.check_poly_constraints evd (snd @@ Evd.sort_context_set sigma) in
  if not check then anomaly Pp.(str where ++ spc () ++ str "Equations missing constraints in " ++
    str (Option.default "(anonymous)" name))

let check_goal ~where ?name env sigma (ctx, ty, s) =
  let () = check_context ~where:(Printf.sprintf "[%s context]" where) ?name env sigma ctx in
  let env = push_rel_context ctx env in
  let () = check_typed ~where:(Printf.sprintf "[%s sort]" where) ?name env sigma (mkSort s) in
  check_typed ~where:(Printf.sprintf "[%s type]" where) ?name env sigma ty

module SimpFun :
sig
  type t

  val make : ?name:string -> (Environ.env -> Evd.evar_map ref -> goal -> open_term * bool * Context_map.context_map) -> t
  (** Invariant for [glopt, continue, c = f env evd (ctx, ty, u)]
      Assumes (in current !evd)
      - env, ctx ⊢ ty : Type@{u}
      Then (at return time in !evd)
      - env, ctx ⊢ c : ty
      - if glopt = Some (ctx', ty', u') then env, ctx' ⊢ ty' : Type@{u'}
  *)

  val apply : t -> Environ.env -> Evd.evar_map ref -> goal -> open_term * bool * Context_map.context_map
end =
struct

type t = string option * (Environ.env -> Evd.evar_map ref -> goal -> open_term * bool * Context_map.context_map)

let make ?name f = (name, f)

let apply (name, f) =
  if !Equations_common.debug then
    fun env evd gl ->
      let () = check_goal ~where:"precondition" ?name env !evd gl in
      let ((ngl, c), continue, map) = f env evd gl in
      let () = check_goal ~where:"result" ?name env !evd gl in
      let () = match ngl with
      | None -> ()
      | Some (gl, _) ->
        check_goal ~where:"subgoal" ?name env !evd gl
      in
      ((ngl, c), continue, map)
  else
    f

end

type simplification_fun = SimpFun.t

let apply_simplification_fun = SimpFun.apply

(* Auxiliary functions. *)

(* Build a term with an evar out of [constr -> constr] function.
   Contrarily to the function below, it does not perform type checking in
   the ambient goal. *)
let build_term_core (env : Environ.env) (evd : Evd.evar_map ref)
  (ngl : goal) (f : EConstr.constr -> EConstr.constr) : open_term =
  let tev =
    let (ctx', ty', u') = ngl in
    let env = push_rel_context ctx' env in
    Equations_common.evd_comb1 (Evarutil.new_evar ~typeclass_candidate:false env) evd ty'
  in
  let c = f tev in
  let ev = EConstr.destEvar !evd tev in
  Some (ngl, ev), c

let checked_applist env evd hd args =
  evd_comb0 (fun sigma -> Typing.checked_applist env sigma hd args) evd
let checked_appvect env evd hd args =
  evd_comb0 (fun sigma -> Typing.checked_appvect env sigma hd args) evd

let build_app_infer_concl (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, _, u) : goal)
  (f : Names.GlobRef.t) ?(inst:EInstance.t option)
  (args : EConstr.constr option list) =
  let tf, ty =
    match inst with
    | Some u ->
      let tf = EConstr.mkRef (f, u) in
      let auctx = Environ.universes_of_global env f in
      let univs = UVars.AbstractContext.instantiate (EConstr.EInstance.kind !evd u) auctx in
      let sigma = Evd.add_poly_constraints !evd univs in
      let ty = Retyping.get_type_of env sigma tf in
      evd := sigma; tf, ty
    | None ->
      match f with
      | Names.GlobRef.VarRef var -> assert false
      | Names.GlobRef.ConstRef cst ->
        let pcst = Equations_common.evd_comb1 (Evd.fresh_constant_instance env) evd cst in
        let pcst = from_peuniverses !evd pcst in
        let tf = Constr.mkConstU pcst in
        let ty = Typeops.type_of_constant_in env pcst in
        of_constr tf, of_constr ty
      | Names.GlobRef.IndRef ind ->
        let pind = Equations_common.evd_comb1 (Evd.fresh_inductive_instance env) evd ind in
        let tf = EConstr.mkIndU pind in
        let ty = Inductiveops.type_of_inductive env pind in
        tf, ty
      | Names.GlobRef.ConstructRef cstr ->
        let pcstr = Equations_common.evd_comb1 (Evd.fresh_constructor_instance env) evd cstr in
        let tf = EConstr.mkConstructU pcstr in
        let ty = Inductiveops.type_of_constructor env pcstr in
        tf, ty
  in
  let env = push_rel_context ctx env in
  let prefix, suffix = CList.map_until (fun o -> o) args in
  let hd = checked_applist env evd tf prefix in
  let rec aux ty args =
    match kind !evd ty, args with
    | Constr.Prod (_, t, c), hd :: tl -> aux (Vars.subst1 hd c) tl
    | Constr.Prod (_, t, _), [] -> t
    | Constr.LetIn (_, b, _, c), args -> aux (Vars.subst1 b c) args
    | Constr.Cast (c, _, _), args -> aux c args
    | _, _ -> failwith "Unexpected mismatch."
  in
  let ty' = aux ty prefix in
  let ty' = Reductionops.whd_beta env !evd ty' in
(*   let u = Retyping.get_sort_of env !evd ty' in *)
  let cont = fun c ->
    let suffix = CList.map (Option.default c) suffix in
    checked_applist env evd hd suffix
  in cont, ty', u

(** Same as above but assumes that the arguments are well-typed in [ctx]. This
    only checks that the application is correct. *)
let build_app (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, u) : goal)
  (f : Names.GlobRef.t) ?(inst:EInstance.t option)
  (args : EConstr.constr option list) : open_term =
  let cont, ty', u' = build_app_infer_concl env evd (ctx, ty, u) f ?inst args in
  build_term_core env evd (ctx, ty', u') cont

let transparent_state env =
  Conv_oracle.get_transp_state (Environ.oracle env)

let unif_flags env =
  let flags = transparent_state env in
  Evarconv.default_flags_of flags

let is_conv (env : Environ.env) (sigma : Evd.evar_map) (ctx : rel_context)
  (t1 : EConstr.t) (t2 : EConstr.t) : bool =
  let env = push_rel_context ctx env in
  match Reductionops.infer_conv ~ts:(transparent_state env) env sigma t1 t2 with
  | Some _ -> true
  | None -> false

(* Build an open term by substituting the second term for the hole in the
 * first term. *)
let compose_term (env : Environ.env) (evd : Evd.evar_map ref)
  ((h1, c1) : open_term) ((h2, c2) : open_term) : open_term =
  match h1 with
  | Some ((ctx1, _, u1), (ev1, _)) ->
      let Evd.EvarInfo ev1_info = Evd.find !evd ev1 in
      let ev1_ctx = Evd.evar_context ev1_info in
      (* Keep only the context corresponding to [ctx1]. *)
      let named_ctx1 = CList.firstn (List.length ctx1) ev1_ctx in
      (* Now keep only the names and make terms out of them. *)
      let subst_ctx1 = List.map (fun decl ->
        let id = Context.Named.Declaration.get_id decl in
        EConstr.mkVar id) named_ctx1 in
      (* Finally, substitute the rels in [c2] to get a valid term for [ev1]. *)
      let c2 = Vars.substl subst_ctx1 c2 in
      evd := Evarsolve.check_evar_instance Evarconv.(conv_fun evar_conv_x) (unif_flags env) env !evd ev1 c2;
      evd := Evd.define ev1 c2 !evd;
      h2, c1
  | None -> assert false

let compose_res (env : Environ.env) (evd : Evd.evar_map ref)
  ((t1, b1, s1) : open_term * bool * Context_map.context_map)
  ((t2, b2, s2) : open_term * bool * Context_map.context_map) : open_term * bool * Context_map.context_map =
    let t = compose_term env evd t1 t2 in
    let s = Context_map.compose_subst env ~sigma:!evd s2 s1 in
      t, b2, s

let safe_fun (f : simplification_fun) : simplification_fun =
SimpFun.make ~name:"safe_fun" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, u) : goal) ->
  let (_, c), _, _ as res = SimpFun.apply f env evd (ctx, ty, u) in
  let env = push_rel_context ctx env in
  evd := Typing.check env !evd c ty;
  res
end

(* Applies [g] to the goal, then [f]. *)
let compose_fun (f : simplification_fun) (g : simplification_fun) :
  simplification_fun =
SimpFun.make ~name:"compose_fun" begin fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let (h1, _), continue, _ as res1 = SimpFun.apply g env evd gl in
  if continue then match h1 with
  | Some (gl', _) ->
      let res2 = SimpFun.apply f env evd gl' in compose_res env evd res1 res2
  | None -> res1
  else res1
end

let is_block env evd (ctx, ty, glu) = 
  let ty = Reductionops.whd_betaiota env !evd ty in
  try let _na, b, _ty, b' = destLetIn !evd ty in
    Equations_common.is_global env !evd (Lazy.force Equations_common.coq_block) b
  with Constr.DestKO -> false

let guard_block (f : simplification_fun) : simplification_fun =
SimpFun.make ~name:"guard_block" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, _, _) as gl : goal) ->
  if is_block env evd gl then build_term_core env evd gl (fun c -> c), false, Context_map.id_subst ctx
  else SimpFun.apply f env evd gl
end

let identity : simplification_fun =
SimpFun.make ~name:"identity" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, u as gl) : goal) ->
  build_term_core env evd gl (fun c -> c), true, Context_map.id_subst ctx
end

let while_fun (f : simplification_fun) : simplification_fun =
SimpFun.make ~name:"while_fun" begin fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let rec aux env evd gl =
    match SimpFun.apply f env evd gl with
    | (Some (gl', _), _), true, _ as res1 ->
        begin try
          let evd' = ref !evd in
          let res2 = aux env evd' gl' in
          let res = compose_res env evd' res1 res2 in
            evd := !evd'; res
        with CannotSimplify _ -> res1 end
    | (_, _), _, _ as res1 -> res1
  in try
    aux env evd gl
  with CannotSimplify _ -> SimpFun.apply identity env evd gl
end

(* Check if a type is a given inductive. *)
let check_inductive env sigma (ind : Names.inductive) : EConstr.types -> bool =
  Equations_common.is_global env sigma (Names.GlobRef.IndRef ind)
(* Check if a term is a given constructor. *)
let check_construct env sigma (constr : Names.constructor) : EConstr.constr -> bool =
  Equations_common.is_global env sigma (Names.GlobRef.ConstructRef constr)
(* Check if a term is a given constant. *)
let check_constant env sigma (cst : Names.Constant.t) : EConstr.constr -> bool =
  Equations_common.is_global env sigma (Names.GlobRef.ConstRef cst)

(* Deconstruct the goal if it's a product. Otherwise, raise CannotSimplify. *)
let check_prod sigma (ty : EConstr.types) : Names.Name.t binder_annot * EConstr.types * EConstr.types =
  let name, ty1, ty2 = try destProd sigma ty
    with Constr.DestKO -> raise (CannotSimplify NotAProduct)
  in name, ty1, ty2

(* Check that the given type is an equality, and some
 * additional constraints if specified. Raise CannotSimplify if it's not
 * the case. Otherwise, return its arguments *)
let check_equality env sigma ctx ?(equal_terms : bool = false)
  ?(var_left : bool = false) ?(var_right : bool = false) (ty : EConstr.types) :
  EConstr.EInstance.t * EConstr.types * EConstr.constr * EConstr.constr =
  let f, args = Equations_common.decompose_appvect sigma ty in
  if not (check_inductive env sigma (Lazy.force EqRefs.eq) f) then
    raise (CannotSimplify FirstHypNotAnEquality);
  let _, u = EConstr.destInd sigma f in
  let tA = args.(0) in
  let tx, ty = args.(1), args.(2) in
  if equal_terms && not (is_conv env sigma ctx tx ty) then
    raise (CannotSimplify FirstHypNotAnEqualityIdentical);
  if var_left && not (EConstr.isRel sigma tx) then
    raise (CannotSimplify FirstHypLHSNotVariable);
  if var_right && not (EConstr.isRel sigma ty) then
    raise (CannotSimplify FirstHypRHSNotVariable);
  u, tA, tx, ty

let decompose_sigma env sigma (t : EConstr.constr) :
  (EInstance.t * EConstr.types * EConstr.constr * EConstr.constr * EConstr.constr) option =
  let f, args = Equations_common.decompose_appvect sigma t in
  if check_construct env sigma (Lazy.force SigmaRefs.sigmaI) f then
    let _, u = EConstr.destConstruct sigma f in
    Some (u, args.(0), args.(1), args.(2), args.(3))
  else None

(** All simplifications are wrapped in with_retry so that their 
  preconditions can be satisfied up-to head-normalization of the goal's
  head type. *)
let hnf_goal ~(reduce_equality:bool) =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, u) : goal) ->
  let glenv = push_rel_context ctx env in
  let reduce c = Tacred.hnf_constr glenv !evd c in
  (* Head-reduce the goal *)
  let ty = reduce ty in
  (* We try to reduce further when the goal is a product. *)
  let ty =
    try
      let name, ty1, ty2 = destProd !evd ty in
      let ty1 = reduce ty1 in
      let ty = mkProd (name, ty1, ty2) in
      (* If the head is an equality, reduce it. *)
      if reduce_equality then 
        try
          let equ, tA, t1, t2 = check_equality env !evd ctx ty1 in
          let t1 = reduce t1 in
          let t2 = reduce t2 in
          let env = push_rel_context ctx env in
          let ty1 = checked_appvect env evd (Builder.equ equ) [| tA; t1; t2 |] in
          EConstr.mkProd (name, ty1, ty2)
        with CannotSimplify _ -> ty
      else ty
    with Constr.DestKO -> ty
  in
  (ctx, ty, u)

let hnf ~reduce_equality : simplification_fun =
SimpFun.make ~name:"hnf" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, u as gl) : goal) ->
  let gl' = hnf_goal ~reduce_equality env evd gl in
  build_term_core env evd gl' (fun c -> c), true, Context_map.id_subst ctx
end

let with_retry (f : simplification_fun) : simplification_fun =
SimpFun.make ~name:"with_retry" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, u) : goal) ->
  try
    (* Be careful with the [evar_map] management. *)
    let evd' = ref !evd in
    let res = SimpFun.apply f env evd' (ctx, ty, u) in
    evd := !evd'; res
  with CannotSimplify _ ->
    (*msg_info (str "Reduce!");*)
    SimpFun.apply f env evd (hnf_goal ~reduce_equality:true env evd (ctx, ty, u))
end

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

(* This function is not accessible by the user for now. It is used to project
 * (if needed) the first component of an equality between sigmas. It will not
 * do anything if it fails. *)
let remove_one_sigma ?(only_nondep=false) () : simplification_fun =
SimpFun.make ~name:"remove_one_sigma" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let equ, _, t1, t2 = check_equality env !evd ctx ty1 in
  let sigu, f, args =
    match decompose_sigma env !evd t1, decompose_sigma env !evd t2 with
    | Some (sigu, tA, tB, tt, tp), Some (_, _, _, tu, tq) ->
        (* Determine the degree of dependency. *)
        if Vars.noccurn !evd 1 ty2 then begin
          (* No dependency in the goal, but maybe there is a dependency in
             the pair itself. *)
          try
            let name', _, tBbody = destLambda !evd tB in
            if Vars.noccurn !evd 1 tBbody then
              (* No dependency whatsoever. *)
              let tsimpl_sigma = Names.GlobRef.ConstRef (Lazy.force EqRefs.simpl_sigma) in
              let tP = Termops.pop tBbody in
              let tB = Termops.pop ty2 in
              let args = [Some tA; Some tP; Some tB; Some tt; Some tu;
                          Some tp; Some tq; None] in
                sigu, tsimpl_sigma, args
            else raise Constr.DestKO
          with
          | Constr.DestKO ->
            if only_nondep then raise (CannotSimplify DependentPair)
            else
              (* Dependency in the pair, but not in the goal. *)
              let tsimpl_sigma = Names.GlobRef.ConstRef (Lazy.force EqRefs.simpl_sigma_dep) in
              let tP = tB in
              let tB = Termops.pop ty2 in
              let args = [Some tA; Some tP; Some tB; Some tt; Some tu;
                          Some tp; Some tq; None] in
              sigu, tsimpl_sigma, args
        end else begin
          try
            let name', _, tBbody = destLambda !evd tB in
            if Vars.noccurn !evd 1 tBbody then
              (* Dependency in the goal, but not in the pair. *)
              let tsimpl_sigma = Names.GlobRef.ConstRef (Lazy.force EqRefs.simpl_sigma_nondep_dep) in
              let tP = Termops.pop tBbody in
              let tB = EConstr.mkLambda (name, ty1, ty2) in
              let args = [Some tA; Some tP; Some tt; Some tu;
                          Some tp; Some tq; Some tB; None] in
              sigu, tsimpl_sigma, args
            else raise Constr.DestKO
          with
          | Constr.DestKO ->
            (* Full dependency *)
            if only_nondep then raise (CannotSimplify DependentPair)
            else
              let tsimpl_sigma = Names.GlobRef.ConstRef (Lazy.force EqRefs.simpl_sigma_dep_dep) in
              let tP = tB in
              let tB = EConstr.mkLambda (name, ty1, ty2) in
              let args = [Some tA; Some tP; Some tt; Some tu;
                          Some tp; Some tq; Some tB; None] in
              sigu, tsimpl_sigma, args
        end
    | _, _ -> raise (CannotSimplify AnomalyReport)
  in
  let sigma, inst, glu = Equations_common.instance_of env !evd ~argu:sigu glu in
  evd := sigma;
  build_app env evd (ctx, ty, glu) f ~inst args, true, Context_map.id_subst ctx
end

let remove_sigma = while_fun (with_retry (remove_one_sigma ()))

let deletion ~(force:bool) : simplification_fun =
SimpFun.make ~name:"deletion" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let u, tA, tx, _ = check_equality env !evd ctx ~equal_terms:true ty1 in
  let subst = Context_map.id_subst ctx in
  if Vars.noccurn !evd 1 ty2 then
    (* The goal does not depend on the equality, we can just eliminate it. *)
    build_term_core env evd (ctx, Termops.pop ty2, glu)
      (fun c -> EConstr.mkLambda (name, ty1, Vars.lift 1 c)), true,
    subst
  else
    let tB = EConstr.mkLambda (name, ty1, ty2) in
    try
      if not !Equations_common.simplify_withUIP then raise Not_found else
        (* We will try to find an instance of UIP for the type [A]. *)
        let tsimpl_uip = Names.GlobRef.ConstRef (Lazy.force EqRefs.simpl_uip) in
        let uip_ty = EConstr.mkApp (Builder.uip evd, [| tA |]) in
        let tuip =
          let env = push_rel_context ctx env in
          Equations_common.evd_comb1
            (Class_tactics.resolve_one_typeclass env) evd uip_ty
        in
        let args = [Some tA; Some tuip; Some tx; Some tB; None] in
        build_app env evd (ctx, ty, glu) tsimpl_uip args, true, subst
    with Not_found ->
      let env = push_rel_context ctx env in
      raise (CannotSimplify (UIPneeded (env, !evd, tA, !Equations_common.simplify_withUIP)))
end

let deletion ~(force:bool) = with_retry (deletion ~force)

let solution ~(dir:direction) : simplification_fun =
SimpFun.make ~name:"solution" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let var_left = match dir with Left -> true | Right -> false in
  let var_right = not var_left in
  let name, ty1, ty2 = check_prod !evd ty in
  let equ, tA, tx, tz = check_equality env !evd ctx ~var_left ~var_right ty1 in
  let trel, term =
    if var_left then tx, tz
    else tz, tx
  in
  let rel = EConstr.destRel !evd trel in
  let () =
    if Int.Set.mem rel (Context_map.dependencies_of_term ~with_red:true env !evd ctx term rel) then
      raise (CannotSimplify VariableOnBothSides)
  in
  (* let () = equations_debug (fun () -> str "solution on " ++ Printer.pr_econstr_env (push_rel_context ctx env) !evd ty) in *)
  let subst, rev_subst = Context_map.new_strengthen env !evd ctx rel term in
  let ctx' = subst.Context_map.src_ctx in
  let trel' = Context_map.mapping_constr !evd subst trel in
  let rel' = EConstr.destRel !evd trel' in
  let term' = Context_map.mapping_constr !evd subst term in
  let tA' = Context_map.mapping_constr !evd subst tA in
  let ty1' = Context_map.mapping_constr !evd subst ty1 in

  (* We will have to generalize everything after [x'] in the new
   * context. *)
  let after', decl', before' = Context_map.split_context (pred rel') ctx' in
  let name' = Context.Rel.Declaration.get_annot decl' in
  (* let after, _, before = Context_map.split_context rel ctx in*)
  
  (* Select the correct solution lemma. *)
  let nondep = Vars.noccurn !evd 1 ty2 in
  let uinst, glu' =
    (* If the equality is not polymorphic, the lemmas will be monomorphic as well *)
    if EConstr.EInstance.is_empty equ then equ, glu
    else let sigma, equ, glu = Equations_common.instance_of env !evd ~argu:equ glu in
      evd := sigma; equ, glu
  in
  let tsolution = begin match var_left, nondep with
  | false, false -> Builder.solution_right_dep
  | false, true -> Builder.solution_right
  | true, false -> Builder.solution_left_dep
  | true, true -> Builder.solution_left end uinst
  in
  let tB', body =
    let body = Context_map.mapping_constr !evd subst ty in
    (* Right now, [body] has an equality at the head that we want
     * to move, in some sense. *)
    let _, _, body = EConstr.destProd !evd body in
    if nondep then
      let body = Termops.pop body in
      let body' = EConstr.it_mkProd_or_LetIn body after' in
        (* [body] is a term in the context [decl' :: before'],
         * whereas [tA'] lives in [ctx']. *)
        EConstr.mkLambda (name', Vars.lift (-rel') tA', body'), body
    else
      (* We make some room for the equality. *)
      let body = Vars.liftn 1 (succ rel') body in
      let body = Vars.subst1 (EConstr.mkRel rel') body in
      let after' = Equations_common.lift_rel_context 1 after' in
      let body' = EConstr.it_mkProd_or_LetIn body after' in
      let body' = EConstr.mkLambda (name, Vars.lift (1-rel') ty1', body') in
        EConstr.mkLambda (name', Vars.lift (-rel') tA', body'), body
  in
  (* [tB'] is a term in the context [before']. We want it in [ctx']. *)
  let tB' = Vars.lift rel' tB' in
  let targs' = Equations_common.extended_rel_vect 1 after' in
  (* [ctx''] is just [ctx'] where we replaced the substituted variable. *)
  let ctx'' = Equations_common.subst_in_ctx rel' term' ctx' in
  let after'', _ = CList.chop (pred rel') ctx'' in
  let ty'' =
    if nondep then
      Vars.substnl [Vars.lift (-rel') term'] (pred rel') body
    else
      let teq_refl = EConstr.mkApp (Builder.eq_refl equ, [| tA'; term' |]) in
      Vars.substnl [Vars.lift (-rel') teq_refl; Vars.lift (-rel') term'] (pred rel') body
  in
  let lsubst = Context_map.single_subst env !evd rel' (Context_map.pat_of_constr env !evd term') ctx' in
  let subst = Context_map.compose_subst env ~sigma:!evd lsubst subst in
  let f = fun c ->
      (* [c] is a term in the context [ctx'']. *)
      let c = EConstr.it_mkLambda_or_LetIn c after'' in
      (* [c] is a term in the context [before']. *)
      let c = Vars.lift rel' c in
      (* [c] is a term in the context [ctx']. *)
      let env = push_rel_context ctx' env in
      let c =
        if nondep then
          checked_appvect env evd tsolution [| tA'; tB'; term'; c; trel' |]
        else
          checked_appvect env evd tsolution [| tA'; term'; tB'; c; trel' |]
      in
      (* We make some room for the application of the equality... *)
      let env = push_rel (Context.Rel.Declaration.LocalAssum (name, ty1')) env in
      let c = Vars.lift 1 c in
      let c = checked_appvect env evd c [| EConstr.mkRel 1 |] in
      (* [targs'] are arguments in the context [eq_decl :: ctx']. *)
      let c = checked_appvect env evd c targs' in
      (* [ty1'] is the type of the equality in [ctx']. *)
      let c = EConstr.mkLambda (name, ty1', c) in
      (* And now we recover a term in the context [ctx]. *)
      Context_map.mapping_constr !evd rev_subst c
  in build_term_core env evd (ctx'', ty'', glu') f, true, subst
end

let whd_all env sigma t = 
  let ts = transparent_state env in
  let flags = RedFlags.red_add_transparent RedFlags.all ts in
  Reductionops.clos_whd_flags flags env sigma t

let nf_all env sigma t = 
  let ts = transparent_state env in
  let flags = RedFlags.red_add_transparent RedFlags.all ts in
  Reductionops.clos_norm_flags flags env sigma t

let pre_solution ~(dir:direction) : simplification_fun =
SimpFun.make ~name:"pre_solution" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let var_left = match dir with Left -> true | Right -> false in
  let var_right = not var_left in
  let name, ty1, ty2 = check_prod !evd ty in
  let _equ, tA, tx, tz = check_equality env !evd ctx ~var_left ~var_right ty1 in
  let trel, term =
    if var_left then tx, tz
    else tz, tx
  in
  let rel = EConstr.destRel !evd trel in
  let () = 
    try let decl = lookup_rel rel ctx in
      if Context.Rel.Declaration.is_local_assum decl then ()
      else raise (CannotSimplify LetBoundVariable)
    with Not_found -> assert false
  in
  (* Check dependencies in both tA and term *)
  if not (Int.Set.mem rel
            (Context_map.dependencies_of_term ~with_red:false env !evd ctx (mkApp (tA, [| term |])) rel)) then
    SimpFun.apply identity env evd (ctx, ty, glu)
  else
    let tA = nf_all (push_rel_context ctx env) !evd tA in
    let term = whd_all (push_rel_context ctx env) !evd term in
    if Int.Set.mem rel (Context_map.dependencies_of_term ~with_red:false env !evd ctx (mkApp (tA, [|term|])) rel) then
      raise (CannotSimplify CannotRemoveDependency)
    else
      let f c = c in
      let eqf, _ = Equations_common.decompose_appvect !evd ty1 in
      let ty1 =
        let env = push_rel_context ctx env in
        if var_left then checked_appvect env evd eqf [| tA; trel; term |]
        else checked_appvect env evd eqf [| tA; term; trel |]
      in
      let ty' = mkProd (name, ty1, ty2) in
      build_term_core env evd (ctx, ty', glu) f, true, Context_map.id_subst ctx
end

let pre_solution ~(dir:direction) = with_retry (pre_solution ~dir)

let is_construct_sigma_2 env sigma f =
  let term = match decompose_sigma env sigma f with
    | Some (_, _, _, _, t) -> t
    | None -> f
  in
  let head, _ = EConstr.decompose_app sigma term in
  EConstr.isConstruct sigma head

(* Auxiliary steps for noConfusion. *)
let maybe_pack : simplification_fun =
SimpFun.make ~name:"maybe_pack" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let equ, tA, t1, t2 = check_equality env !evd ctx ty1 in
  if not (is_construct_sigma_2 env !evd t1 && is_construct_sigma_2 env !evd t2) then
    raise (CannotSimplify NotConstructorEquality);
  let indty =
    try Inductiveops.find_rectype (push_rel_context ctx env) !evd tA
    with Not_found ->
      raise (CannotSimplify NotConstructorEquality);
  in
  let has_noconf () =
    let noconf_ty = EConstr.mkApp (Builder.noConfusion evd, [| tA |]) in
    let env = push_rel_context ctx env in
    try
      let _noconf = Equations_common.evd_comb1
          (Class_tactics.resolve_one_typeclass env) evd noconf_ty in
      true
    with Not_found -> false
  in
  let indfam, args = Inductiveops.dest_ind_type indty in
  if CList.is_empty args then
    SimpFun.apply identity env evd (ctx, ty, glu)
  else if has_noconf () then
    SimpFun.apply identity env evd (ctx, ty, glu)
  else begin
    (* We need to apply [simplify_ind_pack]. *)
    let ind, params = Equations_common.dest_ind_family indfam in
    let evd', tBfull, _, _, valsig, _, _, tA' = Sigma_types.build_sig_of_ind env !evd ind in
    evd := evd';
    let tA' = Vars.substl (List.rev params) tA' in
    (* We will try to find an instance of UIP for the type [A]. *)
    let eqdec_ty = EConstr.mkApp (Builder.uip evd, [| tA' |]) in
    let tdec =
      let env = push_rel_context ctx env in
      try
        Equations_common.evd_comb1
          (Class_tactics.resolve_one_typeclass env) evd eqdec_ty
      with Not_found ->
        raise (CannotSimplify (UIPorNoConfusionneeded (env, !evd, tA', fst ind)))
    in
    if not !Equations_common.simplify_withUIP then
      (let env = push_rel_context ctx env in
       raise (CannotSimplify (NoConfusionHomneeded (env, !evd, tA, fst ind))));
    let tx =
      let _, _, _, tx, _ = Option.get (decompose_sigma env !evd valsig) in
        Vars.substl (CList.rev args) (Termops.pop tx)
    in
    let tsimplify_ind_pack = Names.GlobRef.ConstRef (Lazy.force EqRefs.simplify_ind_pack) in
    let tB = Reductionops.beta_applist !evd (tBfull, params) in
    (* FIXME Inserted this to simplify tB when it has the shape:
               {index & let H := index in foo H}
             Is this correct? *)
    let tB = let env = push_rel_context ctx env in
      Tacred.simpl env !evd tB in
    let tG = EConstr.mkLambda (name, ty1, ty2) in
    let args = [Some tA'; Some tdec; Some tB; Some tx; Some t1; Some t2; Some tG; None] in
    (* Playing a bit with the fire, [t1], [t2] and [tG] are clearly well-typed,
       but it's not clear for the others. It seems to work in practice. *)
    build_app env evd (ctx, ty, glu) tsimplify_ind_pack args, true, Context_map.id_subst ctx
  end
end

let maybe_pack = with_retry maybe_pack

let apply_noconf : simplification_fun =
SimpFun.make ~name:"apply_noconf" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let equ, tA, t1, t2 = check_equality env !evd ctx ty1 in
  if not (is_construct_sigma_2 env !evd t1 && is_construct_sigma_2 env !evd t2) then
    raise (CannotSimplify NotConstructorEquality);
  let noconf_ty = EConstr.mkApp (Builder.noConfusion evd, [| tA |]) in
  let tnoconf =
    let env = push_rel_context ctx env in
    try
      Equations_common.evd_comb1
        (Class_tactics.resolve_one_typeclass env) evd noconf_ty
    with Not_found ->
      raise (CannotSimplify (NoConfusionneeded (env, !evd, tA)))
  in
  let tapply_noconf = Names.GlobRef.ConstRef (Lazy.force EqRefs.apply_noConfusion) in
  let tB = EConstr.mkLambda (name, ty1, ty2) in
  let args = [Some tA; Some tnoconf; Some t1; Some t2; Some tB; None] in
  let inst, glu' =
    (* If the equality is not polymorphic, the lemmas will be monomorphic as well *)
    if EConstr.EInstance.is_empty equ then None, glu
    else let sigma, equ, glu = Equations_common.instance_of env !evd ~argu:equ glu in
      evd := sigma; Some equ, glu
  in
    build_app env evd (ctx, ty, glu') tapply_noconf ?inst args,
    true, Context_map.id_subst ctx
end

let noConfusion = compose_fun (compose_fun (hnf ~reduce_equality:false) apply_noconf) maybe_pack

let simplify_ind_pack_inv : simplification_fun =
SimpFun.make ~name:"simplify_ind_pack" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  (* FIXME Can't ignore _all_ errors? *)
  try
    let reduce c =
      let env = push_rel_context ctx env in
      Tacred.hnf_constr env !evd c (* FIXME? due to refolding this could be ill-typed *)
    in
    let try_decompose ty =
      let f, args = Equations_common.decompose_appvect !evd ty in
      if not (check_constant env !evd (Lazy.force EqRefs.opaque_ind_pack_eq_inv) f) ||
         not (Int.equal 8 (Array.length args)) then
        raise (CannotSimplify PackEqPartialApplication);
      f, args
    in
    let (f, args), ty =
      try try_decompose ty, ty with CannotSimplify _ ->
        let ty = reduce ty in
        try_decompose ty, ty
    in
    let tA = args.(0) in
    let teqdec = args.(1) in
    let tB = args.(2) in
    let tx = args.(3) in
    let tp = args.(4) in
    let tG = args.(6) in
    let teq = args.(7) in
    (* Check that [teq] is [eq_refl]. *)
    let head, _ = decompose_app !evd teq in
    if not (is_global env !evd (Names.GlobRef.ConstructRef (Lazy.force EqRefs.eq_refl)) head) then
      raise (CannotSimplify PackEqAnomaly);
    let tsimplify_ind_pack_inv = Names.GlobRef.ConstRef (Lazy.force EqRefs.simplify_ind_pack_inv) in
    let args = [Some tA; Some teqdec; Some tB; Some tx; Some tp; Some tG; None] in
      build_app env evd (ctx, ty, glu) tsimplify_ind_pack_inv args, true,
      Context_map.id_subst ctx
  with CannotSimplify _ -> SimpFun.apply identity env evd (ctx, ty, glu)
end

let noCycle : simplification_fun =
SimpFun.make ~name:"noCycle" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let equ, tA, t1, t2 = check_equality env !evd ctx ty1 in
  let isct1 = is_construct_sigma_2 env !evd t1 in
  let isct2 = is_construct_sigma_2 env !evd t2 in
  if not (isct1 || isct2) then
    raise (CannotSimplify NotConstructorEquality);
  let nocycle_ty = EConstr.mkApp (Builder.noCycle evd, [| tA |]) in
  let tnocycle =
    let env = push_rel_context ctx env in
    try
      Equations_common.evd_comb1
        (Class_tactics.resolve_one_typeclass env) evd nocycle_ty
    with Not_found ->
      raise (CannotSimplify (NoCycleneeded (env, !evd, tA)))
  in
  let tapply_nocycle =
    if isct1 then
      Names.GlobRef.ConstRef (Lazy.force EqRefs.apply_noCycle_right)
    else Names.GlobRef.ConstRef (Lazy.force EqRefs.apply_noCycle_left)
  in
  let tB = EConstr.mkLambda (name, ty1, ty2) in
  let args = [Some tA; Some tnocycle; Some t1; Some t2; Some tB; None] in
  let inst, glu' =
    (* If the equality is not polymorphic, the lemmas will be monomorphic as well *)
    if EConstr.EInstance.is_empty equ then equ, glu
    else let sigma, equ, glu = Equations_common.instance_of env !evd ~argu:equ glu in
      evd := sigma; equ, glu
  in
  let cont, nocycle, glu' = build_app_infer_concl env evd (ctx, ty, glu) tapply_nocycle ~inst args in
  let subst = Context_map.id_subst ctx in
  try
    let env = push_rel_context ctx env in
    let prf = Equations_common.evd_comb1
        (Class_tactics.resolve_one_typeclass env) evd nocycle in
    (None, cont prf), true, subst
  with Not_found -> (* We inform the user of what is missing *)
    let env = push_rel_context ctx env in
    raise (CannotSimplify (NoCycleCannotInfer (env, !evd, nocycle)))
end

let noCycle = with_retry noCycle

let elim_true : simplification_fun =
SimpFun.make ~name:"elim_true" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  if not (check_inductive env !evd (Lazy.force EqRefs.one) ty1) then
    raise (CannotSimplify FirstHypNotUnit);
  let subst = Context_map.id_subst ctx in
  (* Check if the goal is dependent or not. *)
  if Vars.noccurn !evd 1 ty2 then
    (* Not dependent, we can just eliminate True. *)
    build_term_core env evd (ctx, Termops.pop ty2, glu)
      (fun c -> EConstr.mkLambda (name, ty1, Vars.lift 1 c)), true, subst
  else
    (* Apply the dependent induction principle for True. *)
    let tB = EConstr.mkLambda (name, ty1, ty2) in
    let tone_ind = Names.GlobRef.ConstRef (Lazy.force EqRefs.one_ind_dep) in
    let inst, glu' =
      (* If the equality is not polymorphic, the lemmas will be monomorphic as well *)
      if not (Global.is_polymorphic tone_ind) then EConstr.EInstance.empty, glu
      else let sigma, equ, glu = Equations_common.instance_of env !evd glu in
        evd := sigma; equ, glu
    in
    let args = [Some tB; None] in
      build_app env evd (ctx, ty, glu') tone_ind ~inst args, true, subst
end

let elim_true = with_retry elim_true

let elim_false : simplification_fun =
SimpFun.make ~name:"elim_false" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  if not (check_inductive env !evd (Lazy.force EqRefs.zero) ty1) then
    raise (CannotSimplify FirstHypNotEmpty);
  let subst = Context_map.id_subst ctx in
  let tB, tzero_ind =
  (* Check if the goal is dependent or not. *)
    if Vars.noccurn !evd 1 ty2 then
      let tB = Termops.pop ty2 in
      let tzero_ind = Names.GlobRef.ConstRef (Lazy.force EqRefs.zero_ind) in
        tB, tzero_ind
    else
      let tB = EConstr.mkLambda (name, ty1, ty2) in
      let tzero_ind = Names.GlobRef.ConstRef (Lazy.force EqRefs.zero_ind_dep) in
        tB, tzero_ind
  in
  let inst, glu' =
    (* If the equality is not polymorphic, the lemmas will be monomorphic as well *)
    if not (Global.is_polymorphic tzero_ind) then EConstr.EInstance.empty, glu
    else let sigma, equ, glu = Equations_common.instance_of env !evd glu in
      evd := sigma; equ, glu
    in
  let c = checked_appvect (push_rel_context ctx env) evd (EConstr.mkRef (tzero_ind, inst)) [| tB |] in
  (None, c), true, subst
end

let elim_false = with_retry elim_false

(* Inference mechanism. *)

let infer_step ?(loc:Loc.t option) ~(isSol:bool)
  (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty, glu) : goal) : simplification_step =
  (* The goal does not have to be a product, but if it's not, it has to be
   * an application of [opaque_ind_pack_eq_inv]. *)
  let f, _ = Equations_common.decompose_appvect !evd ty in
  if check_constant env !evd (Lazy.force EqRefs.opaque_ind_pack_eq_inv) f then
    NoConfusionOut
  else begin
    let name, ty1, ty2 = check_prod !evd ty in
    (* First things first, maybe the head of the goal is False or True. *)
    if check_inductive env !evd (Lazy.force EqRefs.zero) ty1 then ElimFalse
    else if check_inductive env !evd (Lazy.force EqRefs.one) ty1 then ElimTrue
    else
    (* We need to destruct the equality at the head
       to analyze it. *)
    let equ, tA, tu, tv = check_equality env !evd ctx ty1 in
    (* FIXME What is the correct way to do it? *)
    let choose u v = if u < v then Left else Right in
    (* If the user wants a solution, we need to respect his wishes. *)
    if isSol then
      if EConstr.isRel !evd tu && EConstr.isRel !evd tv then
        Solution (choose (EConstr.destRel !evd tu) (EConstr.destRel !evd tv))
      else if EConstr.isRel !evd tu then Solution Left
      else if EConstr.isRel !evd tv then Solution Right
      else raise (CannotSimplify BothNotVariable)
    else begin
      let check_occur trel term =
        let rel = EConstr.destRel !evd trel in
          not (Int.Set.mem rel (Context_map.dependencies_of_term ~with_red:true env !evd ctx term rel))
      in
      if EConstr.isRel !evd tu && EConstr.isRel !evd tv && check_occur tu tv then
        Solution (choose (EConstr.destRel !evd tu) (EConstr.destRel !evd tv))
      else if EConstr.isRel !evd tu && check_occur tu tv then Solution Left
      else if EConstr.isRel !evd tv && check_occur tv tu then Solution Right
      else
      let check_ind t =
        let f, _ = EConstr.decompose_app !evd t in
        try ignore (Inductive.find_rectype env (to_constr ~abort_on_undefined_evars:false !evd f)); true
        with Not_found -> false
      in
      let check_construct t =
        let env = push_rel_context ctx env in
        let t = Tacred.hnf_constr env !evd t in
        let f, _ = EConstr.decompose_app !evd t in
        EConstr.isConstruct !evd f
      in
      if check_ind tA && check_construct tu && check_construct tv then
        NoConfusion [loc, Infer_many]
      else
      if is_conv env !evd ctx tu tv then
        Deletion false (* Never force K. *)
      else
      (* Check if [u] occurs in [t] under only constructors. *)
      (* For now we don't care about the type of these constructors. *)
      (* Note that we also don't need to care about binders, since we can
         only go through constructors and nothing else. *)
      let check_occur t u =
        let eq t = eq_constr !evd t u in
        let rec aux t =
          if eq t then raise Termops.Occur;
          let f, args = EConstr.decompose_app !evd t in
          if EConstr.isConstruct !evd f then
            Array.iter aux args
        in try aux t; false
        with Termops.Occur -> true
      in
      if check_occur tu tv || check_occur tv tu then NoCycle
      else
        raise (CannotSimplify CannotInferStep)
    end
  end

let or_fun (f : simplification_fun) (g : simplification_fun) : simplification_fun =
SimpFun.make ~name:"or_fun" begin fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let evd0 = !evd in
  try SimpFun.apply f env evd gl
  with CannotSimplify _ ->
    evd := evd0; SimpFun.apply g env evd gl
end

let or_fun_e1 (f : simplification_fun) (g : simplification_fun) : simplification_fun =
SimpFun.make ~name:"or_fun_e1" begin fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let evd0 = !evd in
  try SimpFun.apply f env evd gl
  with CannotSimplify e ->
    evd := evd0;
    try SimpFun.apply g env evd gl
    with CannotSimplify _ ->
      evd := evd0; raise (CannotSimplify e)
end

let _expand_many rule env evd ((ctx, ty, glu) : goal) : simplification_rules =
  (* FIXME: maybe it's too brutal/expensive? *)
  let ty = whd_all env !evd ty in
  let _, ty, _ = check_prod !evd ty in
  try
    let ty = whd_all env !evd ty in
    let equ, ty, _, _ = check_equality env !evd ctx ty in
    let rec aux ty acc =
      let ty = Reductionops.whd_betaiotazeta env !evd ty in
      let f, args = Equations_common.decompose_appvect !evd ty in
      if check_inductive env !evd (Lazy.force SigmaRefs.sigma) f then
        let next_ty = Reductionops.beta_applist !evd (args.(1), [EConstr.mkRel 1]) in
        aux next_ty (rule :: acc)
      else acc
    in aux ty [rule]
  with CannotSimplify _ -> [rule]

let check_block_notprod : simplification_fun =
SimpFun.make ~name:"check_block_notprod" begin fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty, glu as gl) : goal) ->
    try let _ = destLetIn !evd ty in
      SimpFun.apply identity env evd gl
    with Constr.DestKO ->
    try
      let env = push_rel_context ctx env in
      let ty = whd_all env !evd ty in
      let _na, _ty, _ty' = EConstr.destProd !evd ty in
      raise (CannotSimplify AProduct)
    with Constr.DestKO -> SimpFun.apply identity env evd gl
end

let rec apply_noConfusions () =
  SimpFun.make ~name:"apply_noConfusions" begin fun env evd goal ->
    SimpFun.apply (guard_block 
       (or_fun noConfusion (compose_fun (apply_noConfusions ()) (remove_one_sigma ()))))
       env evd goal
    
end

(* Execution machinery. *)

let rec execute_step : simplification_step -> simplification_fun = function
  | Deletion force -> deletion ~force
  | Solution dir -> compose_fun (solution ~dir:dir) (pre_solution ~dir:dir)
  | NoConfusion rules ->
     compose_fun simplify_ind_pack_inv (compose_fun (simplify rules) noConfusion)
  | NoConfusionOut -> simplify_ind_pack_inv
  | NoCycle -> noCycle
  | ElimTrue -> elim_true
  | ElimFalse -> elim_false

and simplify_one ((loc, rule) : Loc.t option * simplification_rule) :
  simplification_fun =
  let handle_error f =
    SimpFun.make ~name:"handle_error" begin fun env evd gl ->
      try SimpFun.apply f env evd gl
      with CannotSimplify err as exn ->
        Loc.raise ?loc exn
    end
  in
  let wrap get_step =
    let f = SimpFun.make ~name:"wrap" begin fun env evd gl ->
      let step = get_step env evd gl in
        SimpFun.apply (execute_step step) env evd gl
    end in
    let fr = compose_fun f remove_sigma in
    with_retry (or_fun f fr)
  in
  let wrap_handle get_step =
    let f = wrap get_step in
    handle_error f
  in
  match rule with
  | Infer_many ->
     let rec aux () = SimpFun.make ~name:"aux" begin fun env evd gl ->
       let first =
         guard_block
           (or_fun (apply_noConfusions ())
              (or_fun_e1 ((wrap (infer_step ?loc ~isSol:false)))
                (remove_one_sigma ~only_nondep:true ())))
       in
       SimpFun.apply (compose_fun (or_fun check_block_notprod (aux ()))
             first) env evd gl
     end in handle_error (aux ())
  | Step step -> wrap_handle (fun _ _ _ -> step)
  | Infer_one -> handle_error (or_fun (apply_noConfusions ())
                                 (or_fun_e1 (wrap (infer_step ?loc ~isSol:false))
                                    (remove_one_sigma ~only_nondep:true ())))
  | Infer_direction -> wrap_handle (infer_step ?loc ~isSol:true)

and simplify (rules : simplification_rules) : simplification_fun =
  let funs = List.rev_map simplify_one rules in
    match funs with
    | [] -> identity
    | hd :: tl -> List.fold_left compose_fun hd tl

let univ_of_goal env sigma ty =
  let s = Retyping.get_sort_of env sigma ty in
  s

let simplify_tac (rules : simplification_rules) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let glu = univ_of_goal env sigma concl in
    let hyps = Proofview.Goal.hyps gl in
    (* Keep aside the section variables. *)
    let sec_hyps, loc_hyps = CList.partition
      (fun decl ->
        let id = Context.Named.Declaration.get_id decl in
        Termops.is_section_variable_env env id) hyps in
    let env = Environ.reset_context env in
    let env = push_named_context (List.map (fun x -> Environ.SecVar, x) sec_hyps) env in
    (* We want to work in a [rel_context], not a [named_context]. *)
    let ctx, subst = Equations_common.rel_of_named_context sigma loc_hyps in
    let _, rev_subst, _ =
      let err () = assert false in
      Equations_common.named_of_rel_context ~keeplets:true err ctx in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars sigma subst concl in
    (* [ty'] is the expected type of the hole in the term, under the
     * context [ctx']. *)
    Refine.refine ~typecheck:true (fun evars ->
      let evd = ref evars in
      let (_, c), _, _ = SimpFun.apply (simplify rules) env evd (ctx, ty, glu) in
      let c = Vars.substl (List.rev rev_subst) c in
         (!evd, c)))


(* Printing functions. *)

let pr_simplification_step : simplification_step -> Pp.t = function
  | Deletion false -> str "-"
  | Deletion true -> str "-!"
  | Solution (Left) -> str "->"
  | Solution (Right) -> str "<-"
  | NoConfusion rules -> str "$"
  | NoConfusionOut -> str "NoConfusionOut"
  | NoCycle -> str "NoCycle"
  | ElimTrue -> str "ElimTrue"
  | ElimFalse -> str "ElimFalse"

let pr_simplification_rule ((_, rule) : Loc.t option * simplification_rule) :
  Pp.t = match rule with
  | Infer_one -> str "?"
  | Infer_direction -> str "<->"
  | Infer_many -> str "*"
  | Step step -> pr_simplification_step step

let pr_simplification_rules : simplification_rules -> Pp.t =
  prlist_with_sep spc pr_simplification_rule
