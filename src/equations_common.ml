(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Constr
open Termops
open Environ
open Reductionops
open Pp
open Locus
open Context

open List
open Libnames
open Tacmach
open Tactics
open Tacticals

open Ltac_plugin
open Tacexpr

let ($) f g = fun x -> f (g x)
let (&&&) f g (x, y) = (f x, g y)
let id x = x

let to_peuniverses (x, u) = (x, EConstr.EInstance.make u)
let from_peuniverses sigma (x, u) = (x, EConstr.EInstance.kind sigma u)

(* Options. *)
let simplify_withUIP = ref false
let equations_with_funext = ref true
let equations_transparent = ref false
let equations_derive_equations = ref true
let equations_derive_eliminator = ref true

let depr_with_k = Deprecation.make ~since:"equations v1.2" ()
let equations_category = CWarnings.create_category ~name:"equations" ()

let () = Goptions.declare_bool_option {
  Goptions.optdepr  = Some depr_with_k;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "WithK"];
  Goptions.optread  = (fun () -> false);
  Goptions.optwrite = (fun b ->
      if b then
        CErrors.user_err (str"DEPRECATED. Use flag [Equations With UIP] and introduce \
                              an axiom [forall A, Equations.Classes.UIP A] \
                              as a type class instance using [Existing Instance] instead.")
      else simplify_withUIP := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = Some depr_with_k;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "WithKDec"];
  Goptions.optread  = (fun () -> !simplify_withUIP);
  Goptions.optwrite = (fun b -> simplify_withUIP := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = None;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "With"; "UIP"];
  Goptions.optread  = (fun () -> !simplify_withUIP);
  Goptions.optwrite = (fun b -> simplify_withUIP := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = None;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "Transparent"];
  Goptions.optread  = (fun () -> !equations_transparent);
  Goptions.optwrite = (fun b -> equations_transparent := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = None;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "With"; "Funext"];
  Goptions.optread  = (fun () -> !equations_with_funext);
  Goptions.optwrite = (fun b -> equations_with_funext := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = None;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "Derive"; "Equations"];
  Goptions.optread  = (fun () -> !equations_derive_equations);
  Goptions.optwrite = (fun b -> equations_derive_equations := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = None;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "Derive"; "Eliminator"];
  Goptions.optread  = (fun () -> !equations_derive_eliminator);
  Goptions.optwrite = (fun b -> equations_derive_eliminator := b)
}

let { Goptions.get = equations_obligations } =
  Goptions.declare_bool_option_and_ref
    ~key:["Equations";"Obligations"]
    ~value:true
    ()

(* Debugging infrastructure. *)

let debug = ref false

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = None;
  Goptions.optstage = Summary.Stage.Interp;
  Goptions.optkey   = ["Equations"; "Debug"];
  Goptions.optread  = (fun () -> !debug);
  Goptions.optwrite = (fun b -> debug := b)
}

let equations_debug s =
  if !debug then
    Feedback.msg_debug (s ())

let pp   x = Pp.pp_with !Topfmt.std_ft x

let ppenv_sigma f =
  fun x ->
    let env = Global.env () in
    pp (f env (Evd.from_env env) x)

type flags = {
  poly : PolyFlags.t;
  obligations : bool;
  open_proof : bool;
  with_eqns : bool;
  with_ind : bool;
  allow_aliases : bool;
  tactic : unit Proofview.tactic }

let check_term env evd c t =
  ignore(Typing.check env evd c t)

let check_type env evd t =
  ignore(Typing.sort_of env evd t)
      
let typecheck_rel_context env evd ctx =
  let open Context.Rel.Declaration in
  try
  let _ =
    List.fold_right
      (fun rel env ->
	 check_type env evd (get_type rel);
	 Option.iter (fun c -> check_term env evd c (get_type rel)) (get_value rel);
	 EConstr.push_rel rel env)
      ctx env
  in ()
  with e ->
    Printf.eprintf "Exception while typechecking context %s : %s\n"
                   (Pp.string_of_ppcmds (Termops.Internal.print_rel_context (EConstr.push_rel_context ctx env) evd))
                   (Printexc.to_string e);
    raise e

let proper_tails l = snd (List.fold_right (fun _ (t,ts) -> List.tl t, ts @ [t]) l (l, []))

let list_find_map_i f =
  let rec try_find_f n = function
    | [] -> None
    | h::t -> 
      match f n h with
      | Some _ as res -> res 
      | None -> try_find_f (n+1) t
  in
  try_find_f

let array_remove_last a =
  Array.sub a 0 (Array.length a - 1)

let array_chop_last a =
  Array.chop (Array.length a - 1) a

let rev_assoc eq k =
  let rec loop = function
    | [] -> raise Not_found | (v,k')::_ when eq k k' -> v | _ :: l -> loop l 
  in
  loop

let array_filter_map f a =
  let l' =
    Array.fold_right (fun c acc -> 
		      Option.cata (fun r -> r :: acc) acc (f c))
    a []
  in Array.of_list l'

let new_global sigma gr =
  try Evd.fresh_global (Global.env ()) sigma gr
  with e ->
    CErrors.anomaly Pp.(str"new_global raised an error on:" ++ Printer.pr_global gr)

let e_new_global evdref gr =
  let sigma, gr = new_global !evdref gr in
  evdref := sigma; gr

type lazy_ref = Names.GlobRef.t Lazy.t

let equations_lib_ref s = Rocqlib.lib_ref ("equations." ^ s)

let find_global s = lazy (equations_lib_ref s)

let find_constant s evd = e_new_global evd (equations_lib_ref s)

let global_reference id =
  match Smartlocate.global_of_extended_global (Nametab.locate_extended (qualid_of_ident id))
  with
  | Some x -> x
  | None ->
      CErrors.anomaly Pp.(str"global_reference called on non existing " ++ Names.Id.print id)

(* Compute the universe constraints necessary for [t] to typecheck *)
let synthetize_type env sigma t =
  (* unset the guard checking, it is useless for constraints *)
  let flags = Environ.typing_flags env in
  let flags = { flags with Declarations.check_guarded = false } in
  let env = Environ.set_typing_flags flags env in
  Typing.type_of ~refresh:false env sigma t

let synthetize env sigma t =
  fst (synthetize_type env sigma t)

let e_type_of env evd t =
  let evm, t = Typing.type_of ~refresh:false env !evd t in
  evd := evm; t

let enter_goal f =
  let open Proofview.Goal in
  enter (fun gl -> f (env gl) (sigma gl) (concl gl))

let collapse_term_qualities uctx c =
  let open Sorts.Quality in
  let nf_rel r =
    try
      match UState.nf_relevance uctx r with
      | Relevant | Irrelevant as r -> r
      | RelevanceVar _ -> (* hack *) Relevant
    with e ->
          if CErrors.is_sync_anomaly e then Relevant
	  else raise e
  in
  let nf_qvar q = match UState.nf_qvar uctx q with
    | QConstant _ | QGlobal _ as q -> q
    | QVar q -> (* hack *) QConstant QType
  in
  let nf_univ _ = None in
  let rec self () c =
    UnivSubst.map_universes_opt_subst_with_binders ignore self nf_rel nf_qvar nf_univ () c
  in self () c

let make_definition ?(check = true) ?opaque ?(poly=PolyFlags.default) evm ?types b =
  let env = Global.env () in
  let evm = match types with
    | None ->
      if check then synthetize env evm b else evm
    | Some t ->
      let evm = synthetize env evm t in
      let evm, bj =
        if check then
          let evm, u = synthetize_type env evm b in
          evm, { uj_val = t; uj_type = u }
        else
          let bj = Retyping.get_judgment_of env evm b in
          evm, bj
      in
      Typing.check_actual_type env evm bj t
  in
  let evm = Evd.minimize_universes evm in
  let evm0 = evm in
  let to_constr c = collapse_term_qualities (Evd.ustate evm) (EConstr.to_constr evm c) in
  let body = to_constr b in
  let typ = Option.map to_constr types in
  let used = Vars.universes_of_constr body in
  let used' = match typ with
    | None -> Univ.Level.Set.empty
    | Some typ -> Vars.universes_of_constr typ
  in
  let used = Univ.Level.Set.union used used' in
  let evm = Evd.restrict_universe_context evm used in
  let univs = Evd.univ_entry ~poly evm in
  evm0, evm, Declare.definition_entry ~univs ?types:typ body

let declare_constant ?check id body ty ~poly ~kind evd =
  let evm0, evm, ce = make_definition ?check ~opaque:false ~poly evd ?types:ty body in
  let cst = Declare.declare_constant ~name:id (Declare.DefinitionEntry ce) ~kind in
  Flags.if_verbose Feedback.msg_info (str((Id.to_string id) ^ " is defined"));
  if PolyFlags.univ_poly poly then
    let cstr = EConstr.(mkConstU (cst, EInstance.make (UVars.UContext.instance (Evd.to_universe_context evm)))) in
    cst, (evm0, cstr)
  else cst, (evm0, EConstr.UnsafeMonomorphic.mkConst cst)

let eval_mfix = function
| Syntax.MutFix (progs, indexes, decl) ->
  let map i (p, prog) =
    let newidx = indexes.(i) in
    let p = { p with Syntax.program_rec = Some (Structural (MutualOn (Some (newidx, None)))) } in
    let fix = EConstr.mkFix ((indexes, i), decl) in
    (p, prog, fix)
  in
  List.mapi map progs

let declare_mutual ~poly mutual evd =
  let mutual = eval_mfix mutual in
  (* We only type-check the first fix, as all other declarations from the mutual
     block are the same except for the fixpoint index *)
  let evd = match mutual with
  | [] -> evd
  | (_, _, hd) :: _ -> synthetize (Global.env ()) evd hd
  in
  let evd = ref evd in
  let mutual =
    List.map (fun (p, prog, fix) ->
      let ty = p.Syntax.program_orig_type in
      let kn, (evm, term) =
        declare_constant ~check:false p.program_id fix (Some ty) ~poly
          !evd ~kind:Decls.(IsDefinition Fixpoint)
      in
      evd := evm;
      let () = Impargs.declare_manual_implicits false (GlobRef.ConstRef kn) p.program_impls in
      (p, prog, term)) mutual
  in
  !evd, mutual

let make_definition ?opaque ?(poly=PolyFlags.default) evm ?types b =
  let evm', _, t = make_definition ?opaque ~poly evm ?types b in
  evm', t

let instance_constructor (cl,u) args =
  let open Context.Rel.Declaration in
  let lenpars = List.count is_local_assum cl.Typeclasses.cl_context in
  let open EConstr in
  let pars = fst (List.chop lenpars args) in
    match cl.cl_impl with
      | GlobRef.IndRef ind ->
        let ind = ind, u in
          (Some (applist (mkConstructUi (ind, 1), args)),
           applist (mkIndU ind, pars))
      | GlobRef.ConstRef cst ->
        let cst = cst, u in
        let term = match args with
          | [] -> None
          | _ -> Some (List.last args)
        in
          (term, applist (mkConstU cst, pars))
      | _ -> assert false

let declare_instance id ~poly evm ctx cl args =
  let open EConstr in
  let c, t = instance_constructor cl args in
  let term = it_mkLambda_or_LetIn (Option.get c) ctx in
  let typ = EConstr.it_mkProd_or_LetIn t ctx in
  let cst, ecst = declare_constant id term (Some typ) ~poly evm ~kind:Decls.(IsDefinition Instance) in
  let () = Classes.declare_instance (Global.env ()) evm (Some Hints.empty_hint_info) Hints.SuperGlobal (GlobRef.ConstRef cst) in
  cst, ecst

let coq_zero = (find_global "nat.zero")
let coq_succ = (find_global "nat.succ")
let coq_nat = (find_global "nat.type")

let rec coq_nat_of_int sigma = function
  | 0 -> Evd.fresh_global (Global.env ()) sigma (Lazy.force coq_zero)
  | n ->
    let sigma, succ = Evd.fresh_global (Global.env ()) sigma (Lazy.force coq_succ) in
    let sigma, n' = coq_nat_of_int sigma (pred n) in
    sigma, EConstr.mkApp (succ, [| n' |])

let rec int_of_coq_nat c = 
  match Constr.kind c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let fresh_id_in_env ?(avoid=Id.Set.empty) id env =
  Namegen.next_ident_away id (Id.Set.union avoid (Id.Set.of_list (ids_of_named_context (named_context env))))

let coq_fix_proto = (find_global "fixproto")

let compute_sort_quality_or_set l =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, c = Evd.fresh_global env evd (Lazy.force l) in
  let _, s = Reduction.dest_arity env
    (EConstr.to_constr ~abort_on_undefined_evars:false evd (Retyping.get_type_of env evd c)) in
  UnivGen.QualityOrSet.of_sort s

let logic_eq_type = (find_global "equality.type")
let logic_eq_refl = (find_global "equality.refl")
let logic_eq_case = (find_global "equality.case")
let logic_eq_elim = (find_global "equality.elim")
let logic_sort = lazy (compute_sort_quality_or_set logic_eq_type)
let logic_bot = (find_global "bottom.type")
let logic_bot_case = (find_global "bottom.case")
let logic_bot_elim = (find_global "bottom.elim")
let logic_top = (find_global "top.type")
let logic_top_intro = (find_global "top.intro")
let logic_top_elim = (find_global "top.elim")
let logic_conj = (find_global "conj.type")
let logic_conj_intro = (find_global "conj.intro")
let logic_unit = (find_global "unit.type")
let logic_unit_intro = (find_global "unit.intro")
let logic_product = (find_global "product.type")
let logic_pair = (find_global "product.intro")
let logic_wellfounded_class = (find_global "wellfounded.class")
let logic_wellfounded = (find_global "wellfounded.type")
let logic_relation = (find_global "relation.type")
let logic_transitive_closure = (find_global "relation.transitive_closure")

let logic_tele_type = (find_global "tele.type")
let logic_tele_tip = (find_global "tele.tip")
let logic_tele_ext = (find_global "tele.ext")
let logic_tele_interp = (find_global "tele.interp")
let logic_tele_measure = (find_global "tele.measure")
let logic_tele_fix = (find_global "tele.fix")
let logic_tele_fix_functional_type = (find_global "tele.fix_functional_type")
let logic_tele_fix_unfold = (find_global "tele.fix_unfold")
let logic_tele_MR = (find_global "tele.MR")

let logic_tele_type_app = (find_global "tele.type_app")
let logic_tele_forall_type_app = (find_global "tele.forall_type_app")
let logic_tele_forall_uncurry = (find_global "tele.forall_uncurry")
let logic_tele_forall = (find_global "tele.forall")
let logic_tele_forall_pack = (find_global "tele.forall_pack")
let logic_tele_forall_unpack = (find_global "tele.forall_unpack")

let logic_eqdec_class = (find_global "eqdec.class")
let logic_eqdec_dec_eq = (find_global "eqdec.dec_eq")

let logic_uip_class = (find_global "uip.class")
let logic_uip_uip = (find_global "uip.uip")

let logic_signature_class = find_global "signature.class"
let logic_signature_sig = find_global "signature.signature"
let logic_signature_pack = find_global "signature.pack"

let get_fresh sigma r = new_global sigma (Lazy.force r)

let get_efresh r evd = e_new_global evd (Lazy.force r)

let is_lglobal env sigma gr c = EConstr.isRefX env sigma (Lazy.force gr) c

open EConstr

let fresh_sort_in_quality_or_set evd s =
  let evars, sort = Evd.fresh_sort_in_quality !evd s in
  evd := evars; mkSort sort

let fresh_logic_sort evd =
  fresh_sort_in_quality_or_set evd (Lazy.force logic_sort)

let mkapp env evdref t args =
  let evd, c = fresh_global env !evdref (Lazy.force t) in
  let _ = evdref := evd in
    mkApp (c, args)

let refresh_universes_strict env evd t = 
  let evd', t' = Evarsolve.refresh_universes ~onlyalg:true (Some true) env !evd t in
    evd := evd'; t'
    
let mkEq env evd t x y = 
  mkapp env evd logic_eq_type [| refresh_universes_strict env evd t; x; y |]
    
let mkRefl env evd ?inst t x =
  match inst with
  | Some inst ->
    EConstr.mkApp (EConstr.mkRef (Lazy.force logic_eq_refl, inst), [| refresh_universes_strict env evd t; x |])
  | None ->
    mkapp env evd logic_eq_refl [| refresh_universes_strict env evd t; x |]

let dummy_loc = None
type 'a located = 'a Loc.located

let tac_of_string tac args =
  try
    Tacinterp.interp (CAst.(make @@ TacArg(TacCall(make (Libnames.qualid_of_string tac, args)))))
  with Not_found ->
    CErrors.anomaly Pp.(str"Cannot find tactic " ++ str tac)

let get_class sigma c =
  let x = Typeclasses.class_of_constr (Global.env()) sigma c in
    fst (snd (Option.get x))

type esigma = Evd.evar_map ref

type 'a peuniverses = 'a * EConstr.EInstance.t

let functional_induction_class evd =
  let evdref = ref evd in
  let cl = find_constant "funind.class" evdref in
  !evdref, get_class !evdref cl

let functional_elimination_class evd =
  let evdref = ref evd in
  let cl = find_constant "funelim.class" evdref in
  !evdref, get_class !evdref cl

let dependent_elimination_class evd =
  get_class !evd (find_constant "depelim.class" evd)

let coq_noconfusion_class = (find_global "noconfusion.class")
let coq_nocycle_class = (find_global "nocycle.class")

let coq_bang = (find_global "internal.bang")
let coq_inacc = (find_global "internal.inaccessible_pattern")
let coq_block = (find_global "internal.block")
let coq_hide = (find_global "internal.hide_pattern")
let coq_hidebody = (find_global "internal.hidebody")
let coq_add_pattern = (find_global "internal.add_pattern")
let coq_end_of_section_id = Id.of_string "eos"
let coq_the_end_of_the_section = (find_global "internal.the_end_of_the_section")
let coq_end_of_section = (find_global "internal.end_of_section")

let coq_ImpossibleCall evd = find_constant "impossiblecall.class" evd

let unfold_add_pattern =
  lazy (Tactics.unfold_in_concl [(Locus.AllOccurrences,
			     Evaluable.EvalConstRef (Globnames.destConstRef (Lazy.force coq_add_pattern)))])

let subterm_relation_base = "subterm_relation"

let coq_sigma = (find_global "sigma.type")
let coq_sigmaI = (find_global "sigma.intro")

let init_projection gr =
  let cst = Globnames.destConstRef gr in
  let p = Option.get @@ Structures.PrimitiveProjections.find_opt cst in
  Projection.make p false
			
let coq_pr1 = lazy (init_projection (Lazy.force (find_global "sigma.pr1")))
let coq_pr2 = lazy (init_projection (Lazy.force (find_global "sigma.pr2")))
			    
(* Misc tactics *)


let rec head_of_constr sigma t =
  let t = strip_outer_cast sigma t in
    match kind sigma t with
    | Prod (_,_,c2)  -> head_of_constr sigma c2 
    | LetIn (_,_,_,c2) -> head_of_constr sigma c2
    | App (f,args)  -> head_of_constr sigma f
    | _      -> t

let nowhere = { onhyps = Some []; concl_occs = NoOccurrences }

(* Lifting a [rel_context] by [n]. *)
let of_tuple (x, b, t) =
  match b with
  | Some def -> Context.Rel.Declaration.LocalDef (x,def,t)
  | None -> Context.Rel.Declaration.LocalAssum (x, t)

let lift_rel_contextn k n sign =
  let open Context.Rel in
  let open Declaration in
  let rec liftrec k = function
    | rel::sign -> let (na,c,t) = to_tuple rel in
      of_tuple (na,Option.map (Vars.liftn n k) c, Vars.liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (Context.Rel.length sign + k) sign

let lift_rel_context n sign = lift_rel_contextn 0 n sign

let lift_list l = List.map (Vars.lift 1) l

(* let compute_params cst =  *)
(*   let body = constant_value (Global.env ()) cst in *)
(*   let init, n, c =  *)
(*     let ctx, body =  *)
(*       match Constr.kind body with *)
(*       | Lambda _ -> decompose_lam_assum c  *)
(*       | _ -> [], c *)
(*     in *)
(*       (interval 0 (List.length ctx),  *)
(*       List.length ctx, body) *)
(*   in *)
(*   let params_of_args pars n args = *)
(*     Array.fold_left *)
(*       (fun (pars, acc) x -> *)
(* 	match pars with *)
(* 	| [] -> (pars, acc) *)
(* 	| par :: pars -> *)
(* 	    if isRel x then *)
(* 	      if n + par = destRel x then *)
(* 		(pars, par :: acc) *)
(* 	      else (pars, acc) *)
(* 	    else (pars, acc)) *)
(*       (pars, []) args *)
(*   in *)
(*   let rec aux pars n c = *)
(*     match Constr.kind c with *)
(*     | App (f, args) -> *)
(* 	if f = mkConst cst then *)
(* 	  let _, pars' = params_of_args pars n args in *)
(* 	    pars' *)
(* 	else pars *)
(*     | _ -> pars *)
(*   in aux init n c *)

let is_transparent_constant env csts ps c =
  match Structures.PrimitiveProjections.find_opt c with
  | None -> Cset_env.mem (QConstant.canonize env c) csts
  | Some p -> PRset_env.mem (QProjection.Repr.canonize env p) ps

let unfold_head env sigma (ids, csts, ps) c =
  let rec aux c = 
    match kind sigma c with
    | Var id when Id.Set.mem id ids ->
      (match Environ.named_body id env with
      | Some b -> true, of_constr b
      | None -> false, c)
    | Const (cst,u) when is_transparent_constant env csts ps cst ->
	    true, of_constr (Environ.constant_value_in env (cst, EInstance.kind sigma u))
    | App (f, args) ->
      (match aux f with
      | true, f' -> true, Reductionops.whd_betaiota env Evd.empty (mkApp (f', args))
      | false, _ -> 
          let done_, args' = 
            Array.fold_left_i (fun i (done_, acc) arg -> 
        if done_ then done_, arg :: acc 
        else match aux arg with
        | true, arg' -> true, arg' :: acc
        | false, arg' -> false, arg :: acc)
        (false, []) args
          in 
            if done_ then true, mkApp (f, Array.of_list (List.rev args'))
            else false, c)
    | _ -> 
      let done_ = ref false in
      let c' = EConstr.map sigma (fun c -> 
        if !done_ then c else 
          let x, c' = aux c in
            done_ := x; c') c
      in !done_, c'
  in aux c

open CErrors

let unfold_head env sigma db t =
  let st =
    List.fold_left (fun (i,c,p) dbname -> 
      let db = try Hints.searchtable_map dbname 
        with Not_found -> user_err (str "Unknown database " ++ str dbname)
      in
      let (ids, csts, ps) = Hints.Hint_db.unfolds db in
        (Id.Set.union ids i, Cset_env.union csts c, PRset_env.union ps p)) (Id.Set.empty, Cset_env.empty, PRset_env.empty) db
  in
  unfold_head env sigma st t

let autounfold_heads db db' cl =
  let open Proofview.Goal in
  enter begin fun gl ->
  let env = env gl in
  let sigma = sigma gl in
  let eq = 
    (match cl with Some (id, _) -> pf_get_hyp_typ id gl | None -> concl gl)
  in
  let did, c' = 
    match kind sigma eq with
    | App (f, [| ty ; x ; y |]) when EConstr.isRefX env sigma (Lazy.force logic_eq_type) f ->
      let did, x' = unfold_head env sigma db x in
      let did', y' = unfold_head env sigma db' y in
      did && did', EConstr.mkApp (f, [| ty ; x' ; y' |])
    | _ -> false, eq
  in
    if did then
      match cl with
      | Some hyp -> change_in_hyp ~check:true None (make_change_arg c') hyp
      | None -> convert_concl ~cast:false ~check:false c' DEFAULTcast
    else tclFAIL (str "Nothing to unfold")
  end

type hintdb_name = string

let rec db_of_constr c = match Constr.kind c with
  | Const (c,_) -> Id.to_string (Constant.label c)
  | App (c,al) -> db_of_constr c
  | _ -> assert false

let dbs_of_constrs = List.map db_of_constr

(** Bindings to Coq *)

let tacvar_arg h =
  let ipat = Genarg.in_gen (Genarg.rawwit Tacarg.wit_intropattern)
    (CAst.make @@ Tactypes.IntroNaming (Namegen.IntroIdentifier h)) in
    TacGeneric (None, ipat)

let rec_wf_tac h n h' rel =
  CAst.(make @@ TacArg(TacCall(make
    (qualid_of_string "Equations.Subterm.rec_wf_eqns_rel",
    [tacvar_arg h';
     ConstrMayEval (ConstrTerm n);
     ConstrMayEval (ConstrTerm h);
     ConstrMayEval (ConstrTerm rel)]))))


let solve_rec_tac () = tac_of_string "Equations.Equations.solve_rec" []

let pi_tac () = tac_of_string "Equations.CoreTactics.pi" []

let set_eos_tac () = tac_of_string "Equations.CoreTactics.set_eos" []

(* Thos are forward references in Init, that get redefined later *)
let noconf_tac () = tac_of_string "Equations.Init.solve_noconf" []
let noconf_hom_tac () = tac_of_string "Equations.Init.solve_noconf_hom" []
let eqdec_tac () = tac_of_string "Equations.Init.solve_eqdec" []
let simpl_equations_tac () = tac_of_string "Equations.Init.simpl_equations" []
let solve_subterm_tac () = tac_of_string "Equations.Init.solve_subterm" []
let specialize_mutfix_tac () = tac_of_string "Equations.Init.specialize_mutfix" []
let unfold_recursor_tac () = tac_of_string "Equations.Init.unfold_recursor" []
let unfold_recursor_ext_tac () = tac_of_string "Equations.Init.unfold_recursor_ext" []
  
open Libnames

let reference_of_global c = Nametab.shortest_qualid_of_global Names.Id.Set.empty c

let tacident_arg h =
  Reference (qualid_of_ident h)

let find_depelim_module () =
  let gr = Rocqlib.lib_ref "equations.depelim.module" in
  match gr with
  | GlobRef.ConstRef c -> Names.Constant.modpath c
  | _ -> CErrors.anomaly (str"equations.depelim.module is not defined")

let depelim_module = Lazy.from_fun find_depelim_module

let find_depelim_prefix () =
  let modpath = Lazy.force depelim_module in
  let mp = ModPath.to_string modpath in
  mp


let depelim_prefix = Lazy.from_fun find_depelim_prefix

let depelim_tactic s =
  Lazy.force depelim_prefix ^ "." ^ s

let depelim_tac h = tac_of_string "Equations.Init.depelim" [tacident_arg h]

let do_empty_tac h = tac_of_string (depelim_tactic "do_empty") [tacident_arg h]
let depelim_nosimpl_tac h = tac_of_string (depelim_tactic "depelim_nosimpl") [tacident_arg h]
let simpl_dep_elim_tac () = tac_of_string (depelim_tactic "simpl_dep_elim") []
let depind_tac h = tac_of_string (depelim_tactic "depind") [tacident_arg h]
let equations_tac () = tac_of_string (depelim_tactic "equations") []
let find_empty_tac () = tac_of_string (depelim_tactic "find_empty") []

let call_tac_on_ref tac c =
  let var = Names.Id.of_string "x" in
  let tac = Locus.ArgArg (dummy_loc, tac) in
  let val_reference = Geninterp.val_tag (Genarg.topwit Stdarg.wit_constr) in
  (* This is a hack to avoid generating useless universes *)
  let c = Constr.mkRef (c, UVars.Instance.empty) in
  let c = Geninterp.Val.inject val_reference (EConstr.of_constr c) in
  let ist = Tacinterp.{ lfun = Names.Id.Map.add var c Names.Id.Map.empty;
                        extra = TacStore.empty; poly = PolyFlags.default } in
  let var = Reference (Locus.ArgVar CAst.(make var)) in
  let tac = CAst.(make @@ TacArg (TacCall (make (tac, [var])))) in
  ist, tac

let solve_equation () =
  Names.KerName.make (Lazy.force depelim_module) (Id.of_string "solve_equation")

let solve_equation_tac (c : Names.GlobRef.t) =
  let ist, tac = call_tac_on_ref (solve_equation ()) c in
  Tacinterp.eval_tactic_ist ist tac

let impossible_call_tac c =
  let tac = Tacintern.glob_tactic
  (CAst.(make @@ TacArg (TacCall(make
  (Libnames.qualid_of_string (depelim_tactic "impossible_call"),
   [Reference (reference_of_global c)]))))) in
  let val_tac = Genarg.glbwit Tacarg.wit_tactic in
  Genarg.in_gen val_tac tac
(* let impossible_call_tac c = *)
(*   let ist, tac = call_tac_on_ref impossible_call c in *)
(*   let val_tac = Genarg.glbwit Tacarg.wit_tactic in *)
(*   let c = Genarg.in_gen val_tac tac in *)
(*   c *)

open EConstr.Vars
   
let mkProd_or_subst decl c =
  let open Context.Rel.Declaration in
  match get_value decl with
    | None -> mkProd (get_annot decl, get_type decl, c)
    | Some b -> subst1 b c

let mkProd_or_clear sigma decl c =
  if not (dependent sigma (mkRel 1) c) then
    subst1 mkProp c
  else mkProd_or_LetIn decl c

let it_mkProd_or_clear sigma ty ctx = 
  fold_left (fun c d -> mkProd_or_clear sigma d c) ty ctx
      
let mkLambda_or_subst decl c =
  let open Context.Rel.Declaration in
  match get_value decl with
    | None -> mkLambda (get_annot decl, get_type decl, c)
    | Some b -> subst1 b c

let mkLambda_or_subst_or_clear sigma decl c =
  let open Context.Rel.Declaration in
  let (na,body,t) = to_tuple decl in
  match body with
  | None when dependent sigma (mkRel 1) c -> mkLambda (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let mkProd_or_subst_or_clear sigma decl c =
  let open Context.Rel.Declaration in
  let (na,body,t) = to_tuple decl in
  match body with
  | None when dependent sigma (mkRel 1) c -> mkProd (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let it_mkProd_or_subst env sigma ty ctx =
  nf_beta env sigma (List.fold_left
                       (fun c d -> whd_betalet env sigma (mkProd_or_LetIn d c)) ty ctx)

let it_mkProd_or_clean env sigma ty ctx =
  let open Context.Rel.Declaration in
  nf_beta env sigma (List.fold_left
                       (fun c d -> whd_betalet env sigma
			 (if (get_name d) == Anonymous then subst1 mkProp c
                          else mkProd_or_LetIn d c)) ty ctx)

let it_mkLambda_or_subst env ty ctx = 
  whd_betalet env Evd.empty
    (List.fold_left (fun c d -> mkLambda_or_LetIn d c) ty ctx)

let mkLambda_or_clear_LetIn sigma decl c =
  let open Context.Rel.Declaration in
  let (na,body,t) = to_tuple decl in
  match body with
  | None -> mkLambda (na, t, c)
  | Some b ->
    if noccurn sigma 1 c then subst1 b c
    else mkLetIn (na, b, t, c)

let it_mkLambda_or_clear_LetIn sigma ty ctx =
  List.fold_left (fun c d -> mkLambda_or_clear_LetIn sigma d c) ty ctx

let it_mkLambda_or_subst_or_clear sigma ty ctx = 
  (List.fold_left (fun c d -> mkLambda_or_subst_or_clear sigma d c) ty ctx)

let it_mkProd_or_subst_or_clear sigma ty ctx = 
  (List.fold_left (fun c d -> mkProd_or_subst_or_clear sigma d c) ty ctx)


let lift_constrs n cs = List.map (lift n) cs

let ids_of_constr sigma ?(all=false) vars c =
  let rec aux vars c =
    match kind sigma c with
    | Var id -> Id.Set.add id vars
    | App (f, args) -> 
	(match kind sigma f with
	| Construct ((ind,_),_)
	| Ind (ind, _) ->
            let (mib,mip) = Global.lookup_inductive ind in
	      Array.fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold sigma aux vars c)
    | _ -> fold sigma aux vars c
  in aux vars c
    
let decompose_indapp sigma f args =
  match kind sigma f with
  | Construct ((ind,_),_) 
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let e_conv env evdref t t' =
  match Reductionops.infer_conv env !evdref ~pb:Conversion.CONV t t' with
  | Some sigma -> (evdref := sigma; true)
  | None -> false
      
let deps_of_var sigma id env =
  Environ.fold_named_context
    (fun _ decl (acc : Id.Set.t) ->
       let n, b, t = Context.Named.Declaration.to_tuple decl in
       if Option.cata (fun x -> occur_var env sigma id (of_constr x)) false b ||
            occur_var env sigma id (of_constr t) then
        Id.Set.add n.binder_name acc
      else acc)
    env ~init:Id.Set.empty
    
let idset_of_list =
  List.fold_left (fun s x -> Id.Set.add x s) Id.Set.empty

let pr_smart_global f = Pputils.pr_or_by_notation pr_qualid f
let string_of_smart_global = function
  | {CAst.v=Constrexpr.AN ref} -> string_of_qualid ref
  | {CAst.v=Constrexpr.ByNotation (s, _)} -> s

let ident_of_smart_global x = 
  Id.of_string (string_of_smart_global x)

let move_after_deps id c =
  let open Context.Named.Declaration in
  let enter gl =
    let sigma = Proofview.Goal.sigma gl in
    let hyps = Proofview.Goal.hyps gl in
    let deps = collect_vars sigma c in
    let iddeps = 
      collect_vars sigma (Tacmach.pf_get_hyp_typ id gl) in
    let deps = Id.Set.diff deps iddeps in
    let find decl = Id.Set.mem (get_id decl) deps in
    let first = 
      match snd (List.split_when find (List.rev hyps)) with
      | a :: _ -> get_id a
      | [] -> user_err
        Pp.(str"Found no hypothesis on which " ++ Id.print id ++ str" depends")
    in
    Tactics.move_hyp id (Logic.MoveAfter first)
  in Proofview.Goal.enter enter

let assert_replacing id c ty =
  tclTHENFIRST (assert_before_replacing id ty) (exact_no_check c)

let observe s (tac : unit Proofview.tactic) =
  let open Proofview.Notations in
  let open Proofview in
  if not !debug then tac
  else
    Goal.enter (fun gl ->
        let env = Goal.env gl in
        let sigma = Goal.sigma gl in
        Feedback.msg_debug (str"Applying " ++ str s ++ str " on " ++
                            Printer.pr_named_context_of env sigma ++
                            str "=================" ++
                            Printer.pr_econstr_env env sigma (Goal.concl gl));
        (Proofview.tclORELSE
         (Proofview.tclTHEN
            tac
            (Proofview.numgoals >>= fun gls ->
             if gls = 0 then (Feedback.msg_debug (str s ++ str " succeeded"); Proofview.tclUNIT ())
             else Proofview.Goal.enter begin fun gl ->
              let () = Feedback.msg_debug (str "Subgoal: " ++ Printer.Debug.pr_goal gl) in
              Proofview.tclUNIT ()
             end))
         (fun iexn -> Feedback.msg_debug
                        (str"Failed with: " ++
                           (match fst iexn with
                            | Tacticals.FailError (n,expl) ->
                               (str" Fail error " ++ int n ++ str " for " ++ str s ++ spc () ++ Lazy.force expl ++
                                  str " on " ++ Printer.pr_econstr_env env sigma (Goal.concl gl))
                            | Pretype_errors.PretypeError (env, sigma, e) ->
                               (str " Pretype error: " ++ Himsg.explain_pretype_error env sigma e)
                            | _ -> CErrors.iprint iexn));
                Proofview.tclZERO ~info:(snd iexn) (fst iexn))))

(** Compat definitions *)

type rel_context = EConstr.rel_context
type rel_declaration = EConstr.rel_declaration
type named_declaration = EConstr.named_declaration
type named_context = EConstr.named_context

let extended_rel_vect n ctx =
  Context.Rel.instance mkRel n ctx
let extended_rel_list n ctx =
  Context.Rel.instance_list mkRel n ctx
let to_tuple = Context.Rel.Declaration.to_tuple
let to_named_tuple = Context.Named.Declaration.to_tuple
let of_named_tuple = Context.Named.Declaration.of_tuple
let to_context c =
  List.map of_tuple c

let get_type = Context.Rel.Declaration.get_type
let get_value = Context.Rel.Declaration.get_value
let get_name = Context.Rel.Declaration.get_name
let get_annot = Context.Rel.Declaration.get_annot
let get_named_type = Context.Named.Declaration.get_type
let get_named_value = Context.Named.Declaration.get_value
let make_assum n t = Context.Rel.Declaration.LocalAssum (n, t)
let make_def n b t = 
  match b with
  | None -> Context.Rel.Declaration.LocalAssum (n, t)
  | Some b -> Context.Rel.Declaration.LocalDef (n, b, t)

let make_named_def n b t = 
  match b with
  | None -> Context.Named.Declaration.LocalAssum (n, t)
  | Some b -> Context.Named.Declaration.LocalDef (n, b, t)

let lookup_rel = Context.Rel.lookup

let named_of_rel_context ?(keeplets = false) default l =
  let acc, args, _, ctx =
    List.fold_right
      (fun decl (subst, args, ids, ctx) ->
        let decl = Context.Rel.Declaration.map_constr (substl subst) decl in
    let id = match get_name decl with Anonymous -> default () | Name id -> id in
    let d = Named.Declaration.of_rel_decl (fun _ -> id) decl in
	let args = if keeplets ||Context.Rel.Declaration.is_local_assum decl then mkVar id :: args else args in
	  (mkVar id :: subst, args, id :: ids, d :: ctx))
      l ([], [], [], [])
  in acc, rev args, ctx

let rel_of_named_context sigma ctx = 
  List.fold_right (fun decl (ctx',subst) ->
      let (n, b, t) = to_named_tuple decl in
      let decl = make_def (map_annot (fun n -> Name n) n) (Option.map (subst_vars sigma subst) b) (subst_vars sigma subst t) in
      (decl :: ctx', n.binder_name :: subst)) ctx ([],[])

let empty_hint_info = Hints.empty_hint_info

(* Substitute a list of constrs [cstrs] in rel_context [ctx] for variable [k] and above. *)

open Context.Rel.Declaration
  
let map_decl f x =
  match x with
  | LocalAssum (na,x) -> LocalAssum (na, f x)
  | LocalDef (na,b,t) -> LocalDef (na, f b, f t)

let subst_rel_context k cstrs ctx = 
  let (_, ctx') = fold_right 
    (fun decl (k, ctx') ->
      (succ k, map_decl (substnl cstrs k) decl :: ctx'))
    ctx (k, [])
  in ctx'

(* A telescope is a reversed rel_context *)

let subst_telescope cstr ctx = 
  let (_, ctx') = fold_left
    (fun (k, ctx') decl ->
      (succ k, (map_decl (substnl [cstr] k) decl) :: ctx'))
    (0, []) ctx
  in rev ctx'

(* Substitute rel [n] by [c] in [ctx]
   Precondition: [c] is typable in [ctx] using variables 
   above [n] *)
    
let subst_in_ctx (n : int) (c : constr) (ctx : EConstr.rel_context) : EConstr.rel_context =
  let rec aux k after = function
    | [] -> []
    | decl :: before ->
	if k == n then (subst_rel_context 0 [lift (-k) c] (List.rev after)) @ before
	else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let set_in_ctx (n : int) (c : constr) (ctx : EConstr.rel_context) : EConstr.rel_context =
  let rec aux k after = function
    | [] -> []
    | decl :: before ->      
      if k == n then
        (rev after) @ LocalDef (get_annot decl, lift (-k) c, get_type decl) :: before
      else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let get_id decl = Context.Named.Declaration.get_id decl

let fold_named_context_reverse = Context.Named.fold_inside
let map_rel_context = Context.Rel.map
let map_rel_declaration = Context.Rel.Declaration.map_constr
let map_rel_relevance f = List.map (Context.Rel.Declaration.map_relevance f)
let map_named_declaration = Context.Named.Declaration.map_constr
let map_named_context = Context.Named.map
let lookup_named = Context.Named.lookup

let subst_in_named_ctx sigma (n : Id.t) (c : constr) (ctx : EConstr.named_context) : EConstr.named_context =
  let rec aux after = function
    | [] -> []
    | decl :: before ->
       let name = get_id decl in
       if Id.equal name n then (rev after) @ before
       else aux (map_named_declaration (replace_vars sigma [n,c]) decl :: after)
                before
  in aux [] ctx

let pp cmds = Feedback.msg_info cmds

let user_err_loc (loc, pp) =
  CErrors.user_err ?loc pp
let error s = CErrors.user_err (str s)
let errorlabstrm msg = CErrors.user_err msg
let print_error e = CErrors.print e

let nf_betadeltaiota = nf_all
let anomaly ?label pp = CErrors.anomaly ?label pp

let new_evar env evm ?src ty =
  Evarutil.new_evar ~typeclass_candidate:true env evm ?src ty

let new_type_evar env evm ?src rigid =
  Evarutil.new_type_evar env evm rigid ?src
                           
let to_evar_map x = x
let of_evar_map x = x
let evar_absorb_arguments = Evardefine.evar_absorb_arguments

let hintdb_set_transparency cst b db =
  let locality = if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal in
  Hints.add_hints ~locality [db] 
    (Hints.HintsTransparencyEntry (Hints.HintsReferences [Evaluable.EvalConstRef cst], b))

(* Call the really unsafe is_global test, we use this on evar-open terms too *)
let is_global = EConstr.isRefX

let constr_of_global_univ sigma u = of_constr (Constr.mkRef (from_peuniverses sigma u))

let rel_vect n m = Array.map of_constr (rel_vect n m)

let applistc c a = applist (c, a)

let instance_constructor sigma tc args =
  instance_constructor tc args

let decompose_appvect sigma t =
  match kind sigma t with
  | App (f, v) -> (f, v)
  | _ -> (t, [||])

let dest_ind_family fam =
  let ind, fam = Inductiveops.dest_ind_family fam in
  ind, fam

(* XXX: EConstr-versions fo these functions really needed XXX *)
let to_constr = to_constr ~abort_on_undefined_evars:false
let prod_appvect sigma p args =
  of_constr (Term.prod_appvect (to_constr sigma p) (Array.map (to_constr sigma) args))
let beta_appvect sigma p args =
  of_constr (Reduction.beta_appvect (to_constr sigma p) (Array.map (to_constr sigma) args))
let find_rectype env sigma ty =
  let Inductiveops.IndType (ind, args) = Inductiveops.find_rectype env sigma ty in
  ind, args

let splay_prod_n_assum env sigma n =
  let rec prodec_rec env n l c =
    if n = 0 then (l, c)
    else
    let t = whd_allnolet env sigma c in
    match EConstr.kind sigma t with
    | Prod (x,t,c)  ->
        prodec_rec (push_rel (LocalAssum (x,t)) env) (pred n)
          (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) ->
        prodec_rec (push_rel (LocalDef (x,b,t)) env) (pred n)
          (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> prodec_rec env n l c
    | _               ->
      let t' = whd_all env sigma t in
        if EConstr.eq_constr sigma t t' then l,t
        else prodec_rec env n l t'
  in
  prodec_rec env n Context.Rel.empty

type identifier = Names.Id.t

let evd_comb0 f evd =
  let evm, r = f !evd in
  evd := evm; r

let evd_comb1 f evd x =
  let evm, r = f !evd x in
  evd := evm; r

(* Universe related functions *)

[%%if rocq = "9.0"]
let set_leq_sort env = Evd.set_leq_sort env
[%%else]
let set_leq_sort _env = Evd.set_leq_sort
[%%endif]

let nonalgebraic_universe_level_of_universe env sigma u =
  match ESorts.kind sigma u with
  | Sorts.Set | Sorts.Prop | Sorts.SProp ->
    sigma, Univ.Level.set, u
  | Sorts.Type u0 | GSort (_, u0) | Sorts.VSort (_, u0) ->
    match Univ.Universe.level u0 with
    | Some l -> Evd.make_nonalgebraic_variable sigma l, l, u
    | None ->
      let sigma, l = Evd.new_univ_level_variable Evd.univ_flexible sigma in
      let ul = ESorts.make @@ Sorts.sort_of_univ @@ Univ.Universe.make l in
      let sigma = set_leq_sort env sigma u ul in
      sigma, l, ul

let instance_of env sigma ?argu goalu =
  let sigma, goall, goalu = nonalgebraic_universe_level_of_universe env sigma goalu in
  let inst =
    match argu with
    | Some equ ->
      let equ = EConstr.EInstance.kind sigma equ in
      let quals, equarray = UVars.Instance.to_array equ in
      EConstr.EInstance.make (UVars.Instance.of_array (quals, Array.append equarray [| goall |]))
    | None -> EConstr.EInstance.make (UVars.Instance.of_array ([||], [| goall |]))
  in
  sigma, inst, goalu
