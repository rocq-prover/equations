(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Nameops
open Constr
open Context
open Termops
open Declarations
open Inductiveops
open Reductionops
open Pp
open Evarutil
open List
open Globnames
open Tactics
open EConstr
open Equations_common

let mkConstructG c u =
  mkConstructU (destConstructRef (Lazy.force c), u)

let mkIndG c u =
  mkIndU (destIndRef (Lazy.force c), u)

let mkAppG env evd gr args =
  let c = e_new_global evd gr in
  evd_comb1 (fun sigma c -> Typing.checked_appvect env sigma c args) evd c

let applistG env evd gr args =
  mkAppG env evd gr (Array.of_list args)

let mkSig env evd (n, c, t) =
  let args = [| c; mkLambda (n, c, t) |] in
    mkAppG env evd (Lazy.force coq_sigma) args

let constrs_of_coq_sigma env evd t alias = 
  let rec aux env proj c ty =
    match kind !evd c with
    | App (f, args) when is_global env !evd (Lazy.force coq_sigmaI) f && 
	                   Array.length args = 4 ->
       let ty = Retyping.get_type_of env !evd args.(1) in
	(match kind !evd ty with
          | Prod (n, b, t) ->
            (* sigma is not sort poly (at least for now) *)
            let p1 = mkProj (Lazy.force coq_pr1, ERelevance.relevant, proj) in
            let p2 = mkProj (Lazy.force coq_pr2, ERelevance.relevant, proj) in
	    (n, args.(2), p1, args.(0)) ::
              aux (push_rel (of_tuple (n, None, b)) env) p2 args.(3) t
	| _ -> raise (Invalid_argument "constrs_of_coq_sigma"))
    | _ -> [(anonR, c, proj, ty)]
  in aux env alias t (Retyping.get_type_of env !evd t)

let decompose_coq_sigma env sigma t = 
  let s = Lazy.force coq_sigma in
    match kind sigma t with
    | App (f, args) when is_global env sigma s f && Array.length args = 2 ->
       let ind, u = destInd sigma f in
         Some (u, args.(0), args.(1))
    | _ -> None

let decompose_indapp sigma f args =
  match kind sigma f with
  | Construct ((ind,_),_)
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args


(* let sigT_info = lazy (make_case_info (Global.env ()) (Globnames.destIndRef (Lazy.force sigT).typ) LetStyle) *)

let telescope_intro env sigma len tele =
  let rec aux n ty =
    let ty = Reductionops.whd_all env sigma ty in
    match kind sigma ty with
    | App (sigma_ty, [| a; p |]) ->
      let sigma_ty, u = destInd sigma sigma_ty in
      let p =
        match kind sigma p with
        | Lambda (na, t, b) ->
          mkLambda (na, t, Reductionops.whd_all
                      (push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env) sigma b)
        | _ -> p
      in
      let sigmaI = mkApp (mkRef (Lazy.force coq_sigmaI, u),
                          [| a; p; mkRel n; aux (pred n) (beta_applist sigma (p, [mkRel n])) |]) in
      sigmaI
    | _ -> mkRel n
  in aux len tele

let telescope_of_context env sigma ctx =
  let sigma, teleinterp = new_global sigma (Lazy.force logic_tele_interp) in
  let _, u = destConst sigma teleinterp in
  let rec aux = function
    | [] -> raise (Invalid_argument "Cannot make telescope out of empty context")
    | [decl] ->
      mkApp (mkRef (Lazy.force logic_tele_tip, u), [|get_type decl|])
    | d :: tl ->
      let ty = get_type d in
      mkApp (mkRef (Lazy.force logic_tele_ext, u), [| ty; mkLambda (get_annot d, ty, aux tl) |])
  in
  let tele = aux (List.rev ctx) in
  let tele_interp = mkApp (teleinterp, [| tele |]) in
  (* Infer universe constraints *)
  let sigma, _ = Typing.type_of env sigma tele_interp in
  sigma, tele, tele_interp

(* Given a context ⊢ Γ, returns
  - ⊢ Tel(Γ) : Type (iterated Σ-type built out of Γ)
  - p : Tel(Γ) ⊢ Ctx(Γ) (a context of let-bindings made of each projection in order)
  - Γ ⊢ Intro(Γ) : Tel(Γ) (iterated constructors)
*)
let telescope env evd = function
  | [] -> assert false
  | [d] -> let (n, _, t) = to_tuple d in t, [of_tuple (n, Some (mkRel 1), Vars.lift 1 t)],
                                        mkRel 1
  | d :: tl ->
      let (n, _, t) = to_tuple d in
      let len = succ (List.length tl) in
      let ts = Retyping.get_sort_of (push_rel_context tl env) !evd t in
      let ts = ESorts.kind !evd ts in
      let ty, tys =
        let rec aux (ty, tyuniv, tys) ds =
          match ds with
          | [] -> (ty, tys)
          | d :: ds ->
            let (n, b, t) = to_tuple d in
            let pred = mkLambda (n, t, ty) in
            let env = push_rel_context ds env in
            let sigty = mkAppG env evd (Lazy.force coq_sigma) [|t; pred|] in
            let _, u = destInd !evd (fst (destApp !evd sigty)) in
            let _, ua = UVars.Instance.to_array (EInstance.kind !evd u) in
            let l = Sorts.sort_of_univ @@ Univ.Universe.make ua.(0) in
            (* Ensure that the universe of the sigma is only >= those of t and pred *)
            let open UnivProblem in
            let enforce_leq env sigma t cstr =
              let ts = Retyping.get_sort_of env sigma t in
              let ts = ESorts.kind sigma ts in
              UnivProblem.Set.add (ULe (ts, l)) cstr
            in
            let cstrs = enforce_leq env !evd t (UnivProblem.Set.add (ULe (tyuniv, l)) UnivProblem.Set.empty) in
            let () = evd := Evd.add_constraints !evd cstrs in
            aux (sigty, l, (u, pred) :: tys) ds
        in aux (t, ts, []) tl
      in
      let constr, _ = 
	List.fold_right (fun (u, pred) (intro, k) ->
	  let pred = Vars.lift k pred in
	  let (n, dom, codom) = destLambda !evd pred in
	  let intro =
            mkApp (constr_of_global_univ !evd (Lazy.force coq_sigmaI, u),
                   [| dom; pred; mkRel k; intro|]) in
	    (intro, succ k))
	  tys (mkRel 1, 2)
      in
      let (last, _, subst) = List.fold_right2
	(fun pred d (prev, k, subst) ->
          let (n, b, t) = to_tuple d in
          (* sigma is not sort poly (at least for now) *)
          let proj1 = mkProj (Lazy.force coq_pr1, ERelevance.relevant, prev) in
          let proj2 = mkProj (Lazy.force coq_pr2, ERelevance.relevant, prev) in
	    (Vars.lift 1 proj2, succ k, of_tuple (n, Some proj1, Vars.liftn 1 k t) :: subst))
	(List.rev tys) tl (mkRel 1, 1, [])
      in ty, (of_tuple (n, Some last, Vars.liftn 1 len t) :: subst), constr

let sigmaize ?(liftty=0) env0 evd pars f =
  let env = push_rel_context pars env0 in
  let ty = Retyping.get_type_of env !evd f in
  let ctx, concl = whd_decompose_prod_decls env !evd ty in
  let ctx = EConstr.Vars.smash_rel_context ctx in
  let argtyp, letbinders, make = telescope env evd ctx in
    (* Everyting is in env, move to index :: letbinders :: env *) 
  let lenb = List.length letbinders in
  let pred =
    mkLambda (nameR (Id.of_string "index"), argtyp,
	      it_mkProd_or_LetIn
	        (mkApp (Vars.lift (succ lenb) f, 
		        rel_vect 0 lenb))
	        letbinders)
  in
  let tyargs = [| argtyp; pred |] in
  let tysig = mkAppG env evd (Lazy.force coq_sigma) tyargs in
  let indexproj = Lazy.force coq_pr1 in
  let valproj = Lazy.force coq_pr2 in
  let indices = 
    (List.rev_map (fun l -> Vars.substl (tl l) (hd l)) 
     (Equations_common.proper_tails (List.map (fun d -> Option.get (pi2 (to_tuple d))) letbinders)))
  in
  let valsig =
    let argtyp = Vars.lift (succ lenb) argtyp in
    let pred = 
      mkLambda (nameR (Id.of_string "index"), argtyp,
	       it_mkProd_or_LetIn
		 (mkApp (Vars.lift (2 * succ lenb) f,
			rel_vect 0 lenb))
		 (Equations_common.lift_rel_contextn 1 (succ lenb) letbinders))
    in
    let (_, u) = destInd !evd (fst @@ destApp !evd tysig) in
    mkApp (mkRef (Lazy.force coq_sigmaI, u), [|argtyp; pred; Vars.lift 1 make; mkRel 1|])
  in
  let pred = it_mkLambda_or_LetIn pred pars in
  let _ = e_type_of env0 evd pred in
  let () = evd := Evd.minimize_universes !evd in
    (argtyp, pred, pars, indices,
     indexproj, valproj, valsig, tysig)

let ind_name ind = Nametab.basename_of_global (GlobRef.IndRef ind)


let signature_class evd =
  let evd, c = get_fresh evd logic_signature_class in
    evd, fst (snd (Option.get (Typeclasses.class_of_constr (Global.env()) evd c)))

let build_sig_of_ind env sigma (ind,u as indu) =
  let (mib, oib as _mind) = Inductive.lookup_mind_specif env ind in
  let ctx = inductive_alldecls env indu in
  let ctx = EConstr.Vars.smash_rel_context ctx in
  let lenpars = mib.mind_nparams_rec in
  let lenargs = List.length ctx - lenpars in
  if lenargs = 0 then
    user_err_loc (None,
		 str"No signature to derive for non-dependent inductive types");
  let args, pars = List.chop lenargs ctx in
  let parapp = mkApp (mkIndU indu, extended_rel_vect 0 pars) in
  let fullapp = mkApp (mkIndU indu, extended_rel_vect 0 ctx) in
  let evd = ref sigma in
  let idx, pred, pars, _, _, _, valsig, _ = 
    sigmaize env evd pars parapp 
  in
  let sigma = !evd in
    sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx

let nf_econstr sigma c = Evarutil.nf_evar sigma c

let declare_sig_of_ind env sigma ~poly (ind,u) =
  let sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx =
    build_sig_of_ind env sigma (ind, u) in
  let indid = ind_name ind in
  let simpl = Tacred.simpl env sigma in
  let sigma = Evd.minimize_universes sigma in
  let fullapp = nf_econstr sigma fullapp in
  let idx = nf_econstr sigma idx in
  let _, (sigma, indsig) =
    let indsigid = add_suffix indid "_sig" in
    declare_constant indsigid pred
        None ~poly sigma ~kind:Decls.(IsDefinition Definition)
  in
  let pack_id = add_suffix indid "_sig_pack" in
  let _, (sigma, pack_fn) =
    let vbinder = of_tuple (nameR (add_suffix indid "_var"), None, fullapp) in
    let term = it_mkLambda_or_LetIn valsig (vbinder :: ctx) 
    in
    (* let rettype = mkApp (mkConst indsig, extended_rel_vect (succ lenargs) pars) in *)
      declare_constant pack_id (simpl term)
	None (* (Some (it_mkProd_or_LetIn rettype (vbinder :: ctx))) *)
        ~poly sigma
	~kind:Decls.(IsDefinition Definition)
  in
  let sigma = if not (PolyFlags.univ_poly poly) then Evd.from_env (Global.env ()) else sigma in
  let sigma, c = signature_class sigma in
  let signature_id = add_suffix indid "_Signature" in
  let inst = 
    declare_instance signature_id
      ~poly sigma ctx c
      [fullapp; Vars.lift lenargs idx;
       mkApp (indsig, extended_rel_vect lenargs pars);
       mkApp (pack_fn, extended_rel_vect 0 ctx)]
  in
  Extraction_plugin.Table.extraction_inline true
                                            [Libnames.qualid_of_ident pack_id];
  Extraction_plugin.Table.extraction_inline true
                                            [Libnames.qualid_of_ident signature_id];
  inst

let () =
  let fn ~pm env sigma ~poly c =
    let _ = declare_sig_of_ind env sigma ~poly c in
    pm
  in
  Ederive.(register_derive
            { derive_name = "Signature";
              derive_fn = make_derive_ind fn })

let warn_auto_inline = 
  CWarnings.create ~name:"signature-auto-inline" ~category:equations_category 
    (fun msg -> msg) 

let get_signature env sigma0 ty =
  try
    let sigma, (idx, _) =
       new_type_evar env sigma0 Evd.univ_flexible
        ~src:(dummy_loc, Evar_kinds.InternalHole) in
    let sigma, (signaturety, _) =
       new_type_evar env sigma Evd.univ_flexible
        ~src:(dummy_loc, Evar_kinds.InternalHole) in
    let sigma, signature =
      new_evar env sigma (mkProd (anonR, idx, Vars.lift 1 signaturety))
    in
    let sigma, cl = get_fresh sigma logic_signature_class in
    let inst = mkApp (cl, [| ty; idx; signature |]) in
    let sigma, tc = Class_tactics.resolve_one_typeclass env sigma inst in
    (* let _, u = destConst sigma (fst (destApp sigma inst)) in *)
    (* let ssig = mkApp (mkConstG logic_signature_sig u, [| ty; idx; tc |]) in *)
    let ssig = signature in
    (* let spack = mkApp (mkConstG logic_signature_pack u, [| ty; idx; tc |]) in *)
    let spack = Reductionops.whd_all env sigma tc in
      (sigma, nf_evar sigma ssig, nf_evar sigma spack)
  with Not_found ->
    let pind, args = Inductive.find_rectype env (to_constr sigma0 ty) in
    let sigma, pred, pars, _, valsig, ctx, _, _ =
      build_sig_of_ind env sigma0 (to_peuniverses pind) in
    warn_auto_inline (str "Automatically inlined signature for type " ++
    Printer.pr_pinductive env sigma pind ++ str ". Use [Derive Signature for " ++
    Printer.pr_pinductive env sigma pind ++ str ".] to avoid this.");
    let indsig = pred in
    let vbinder = of_tuple (anonR, None, ty) in
    let pack_fn = it_mkLambda_or_LetIn valsig (vbinder :: ctx) in
    let args = List.map of_constr args in
    let pack_fn = beta_applist sigma (pack_fn, args) in
      (sigma, nf_evar sigma (mkApp (indsig, Array.of_list args)),
       nf_evar sigma pack_fn)

(* let generalize_sigma env sigma c packid = *)
(*   let ty = Retyping.get_type_of env sigma c in *)
(*   let value, typ = mk_pack env sigma ty in *)
(*   let valsig = value c in *)
(*   let setvar = letin_tac None (Name packid) valsig (Some typ) nowhere in *)
(*   let geneq = generalize [mkCast (mkRefl typ (mkVar packid),  *)
(* 					 DEFAULTcast, mkEq typ (mkVar packid) valsig)] in *)
(*   let clear = clear_body [packid] in *)
(*   let movetop = move_hyp true packid (Tacexpr.MoveToEnd false) in *)
(*     tclTHENLIST [setvar; geneq; clear; movetop] *)

let pattern_sigma ~assoc_right c hyp env sigma =
  let open Tacticals in
  let evd = ref sigma in
  let terms = constrs_of_coq_sigma env evd c (mkVar hyp) in
  let terms =
    if assoc_right then terms
    else match terms with
         | (x, t, p, rest) :: term :: _ -> 
	    constrs_of_coq_sigma env evd t p @ terms
         | _ -> terms
  in
  let pat x = Patternops.pattern_of_constr env !evd x in
  let terms = 
    if assoc_right then terms
    else match terms with
         | (x, t, p, rest) :: _ :: _ -> terms @ constrs_of_coq_sigma env evd t p 
         | _ -> terms
  in
  let projs = List.map (fun (x, t, p, rest) -> (pat t, make_change_arg p)) terms in
  let projabs =
    tclTHENLIST 
      ((if assoc_right then rev_map
        else List.map) (fun (t, p) -> (change ~check:true (Some t) p Locusops.onConcl)) projs) in
    tclTHEN (Proofview.Unsafe.tclEVARS !evd) projabs
			 
let curry_left_hyp env sigma c t =
  let aux c t na u ty pred concl =
    let (n, idx, dom) = destLambda sigma pred in
    let newctx = [of_tuple (na, None, dom); of_tuple (n, None, idx)] in
    let tuple = mkApp (mkConstructG coq_sigmaI u,
		       [| Vars.lift 2 ty; Vars.lift 2 pred; mkRel 2; mkRel 1 |])
    in
    let term = it_mkLambda_or_LetIn (mkApp (Vars.lift 2 c, [| tuple |])) newctx in
    let typ = it_mkProd_or_LetIn (Vars.subst1 tuple (Vars.liftn 2 2 concl)) newctx in
      (term, typ)
  in
  let rec curry_index c t =
    match kind sigma t with
    | Prod (na, dom, concl) ->
       (match decompose_coq_sigma env sigma dom with
	| None -> (c, t)
	| Some (u, ty, pred) ->
	   let term, typ = aux c t na u ty pred concl in
	   match kind sigma typ with
	   | Prod (na', dom', concl') ->
	      let body' = pi3 (destLambda sigma term) in
	      let c, t = curry_index body' concl' in
	      mkLambda (na', dom', c), mkProd (na', dom', t)
	   | _ -> (term, typ))
    | _ -> (c, t)
  in
  let curry c t =
    match kind sigma t with
    | Prod (na, dom, concl) ->
       (match decompose_coq_sigma env sigma dom with
	| None -> None
	| Some (inst, ty, pred) ->
	   let term, typ = aux c t na inst ty pred concl in
	   let c, t = curry_index term typ in
	     Some (c, t))
    | _ -> None
  in curry c t

let curry env sigma na c =
  let rec make_arg na t =
    match decompose_coq_sigma env sigma t with
    | None -> 
       if is_global env sigma (Lazy.force logic_unit) t then
         let _, u = destInd sigma t in
         [], constr_of_global_univ sigma (Lazy.force logic_unit_intro, u)
       else [of_tuple (na,None,t)], mkRel 1
    | Some (u, ty, pred) ->
       let na, _, codom =
         if isLambda sigma pred then destLambda sigma pred 
         else (anonR, ty, mkApp (pred, [|mkRel 1|])) in
       let ctx, rest = make_arg na codom in
       let len = List.length ctx in 
       let tuple = 
         mkApp (mkConstructG coq_sigmaI u,
		[| Vars.lift (len + 1) ty; Vars.lift (len + 1) pred; mkRel (len + 1); rest |])
       in
       ctx @ [of_tuple (na, None, ty)], tuple
  in
  make_arg na c

let uncurry_hyps name =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter (fun gl ->
    let hyps = Goal.hyps gl in
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let hyps, _ =
      List.split_when (fun d ->
          is_global env sigma (Lazy.force coq_end_of_section) (get_named_type d)
          || is_section_variable_env env (get_id d)) hyps in
    let ondecl (sigma, acc, ty) d =
      let (dna, _, dty) = to_named_tuple d in
      let sigma, sigmaI = new_global sigma (Lazy.force coq_sigmaI) in
      let _, u = destConstruct sigma sigmaI in
      let types = [| dty; mkNamedLambda sigma dna dty ty |] in
      let app = mkApp (sigmaI, Array.append types [| mkVar dna.binder_name; acc |]) in
      (sigma, app, mkApp (mkIndG coq_sigma u, types))
    in
    let sigma, unit = get_fresh sigma logic_unit_intro in
    let sigma, unittype = get_fresh sigma logic_unit in
    let sigma, term, ty = 
      fold_named_context_reverse 
        ondecl ~init:(sigma, unit, unittype) hyps
    in
    let sigma, _ = Typing.type_of env sigma term in
    Proofview.Unsafe.tclEVARS sigma <*>
      Tactics.letin_tac None (Name name) term (Some ty) nowhere )

let uncurry_call env sigma fn c =
  let hd', args' = decompose_app sigma fn in
  let hd, args = decompose_app sigma c in
  let params, args = Array.chop (Array.length args') args in
  let hd = mkApp (hd, params) in
  let ty = Retyping.get_type_of env sigma hd in
  let ctx, _ = Reductionops.whd_decompose_prod_decls env sigma ty in
  let ctx =
    let open Context.Rel.Declaration in
    let rec aux env ctx args =
      match ctx, args with
      | LocalAssum (na, t) as decl :: decls, arg :: args ->
        if isSort sigma t then
          let ty = Retyping.get_type_of env sigma arg in
          LocalAssum (na, ty) :: aux env decls args
        else decl :: aux env decls args
      | LocalDef _ as decl :: decls, args ->
        decl :: aux env decls args
      | [], _ :: _ -> assert false
      | ctx, [] -> []
    in List.rev (aux env (List.rev ctx) (Array.to_list args))
  in
  let evdref = ref sigma in
  if CList.is_empty ctx then 
    user_err_loc (None, Pp.str"No arguments to uncurry");
  (* let ctx = (Anonymous, None, concl) :: ctx in *)
  let sigty, sigctx, constr = telescope env evdref ctx in
  let app = Vars.substl (Array.rev_to_list args) constr in
  let fnapp = mkApp (hd, rel_vect 0 (List.length sigctx)) in
  let fnapp = it_mkLambda_or_subst env fnapp sigctx in
  let projsid = nameR (Id.of_string "projs") in
  let fnapp_ty = Retyping.get_type_of
      (push_rel_context [Context.Rel.Declaration.LocalAssum (projsid, sigty)] env)
      !evdref fnapp in
  (* TODO: build (packargs, fn packargs.projs) = (args, c) equality *)
  let sigma, sigmaI = get_fresh !evdref coq_sigmaI in
  let packed =
    mkApp (sigmaI, [| sigty; mkLambda (projsid, sigty, fnapp_ty); mkRel 1; fnapp |])
  in
  let sigma, _ =
    Typing.type_of (push_rel_context [Context.Rel.Declaration.LocalAssum (projsid, sigty)] env) sigma packed
  in
  sigma, app, packed, sigty

(* Produce parts of a case on a variable, while introducing cuts and
 * equalities when necessary.
 * This function requires a full rel_context, a rel to eliminate, and a goal.
 * It returns:
 *   - a context [ctx'];
 *   - a return type valid under [ctx'];
 *   - the type of the branches of the case;
 *   - a context_map for each branch;
 *   - a number of cuts;
 *   - a reverse substitution from [ctx] to [ctx'];
 *   - a list of terms in [ctx] to apply to the case once it is built;
 *   - a boolean about the need for simplification or not. *)
let smart_case (env : Environ.env) (evd : Evd.evar_map ref)
  (ctx : rel_context) (rel : int) (goal : EConstr.types) :
    rel_context * EConstr.types *
    (EConstr.types * int * Context_map.context_map) array *
    int * Context_map.context_map * EConstr.constr list * bool =
  let after, rel_decl, before = Context_map.split_context (pred rel) ctx in
  let rel_ty = Context.Rel.Declaration.get_type rel_decl in
  let rel_ty = Vars.lift rel rel_ty in
  let rel_t = EConstr.mkRel rel in
  (* Fetch some information about the type of the variable being eliminated. *)
  let pind, args = Inductiveops.find_inductive env !evd rel_ty in
  let mib, oib = Global.lookup_inductive (fst pind) in
  let params, indices = List.chop mib.mind_nparams args in
  (* The variable itself will be treated for all purpose as one of its indices. *)
  let indices = indices @ [rel_t] in
  let indfam = Inductiveops.make_ind_family (pind, params) in
  let arity_ctx = Inductiveops.make_arity_signature env !evd true indfam in
  let rev_arity_ctx = List.rev arity_ctx in

  (* Firstly, we need to analyze each index to decide if we should introduce
   * an equality for it or not. *)
  (* For each index of the type, we _omit_ it if and only if
   *   1) It is a variable.
   *   2) It did not appear before.
   *   3) Its type does not depend on something that was not omitted before.
  *)

  (* ===== FORWARD PASS ===== *)
  let rec compute_omitted prev_indices indices prev_ctx ctx omitted candidate nb =
    match indices, ctx with
    | [], [] -> omitted, nb, prev_indices, candidate
    | idx :: indices, decl :: ctx ->
        let omit, cand =
          (* Variable. *)
          if not (isRel !evd idx) then None, None
          (* Linearity. *)
          else if List.exists (Termops.dependent !evd idx) params then None, None
          else if List.exists (Termops.dependent !evd idx) prev_indices then None, None
          (* Dependency. *)
          else
            let rel = EConstr.destRel !evd idx in
            let decl_ty = Context.Rel.Declaration.get_type decl in
            let deps = Termops.free_rels !evd decl_ty in
            let omit =
              Int.Set.fold (fun x b ->
                b && try Option.has_some (List.nth omitted (x-1))
                with Failure _ | Invalid_argument _ -> true) deps true
            in (if omit then Some rel else None), Some rel
        in
        compute_omitted (idx :: prev_indices) indices
                        (decl :: prev_ctx) ctx
                        (omit :: omitted)
                        (cand :: candidate)
                        (if Option.has_some omit then nb else succ nb)
    | _, _ -> assert false
  in
  (* [rev_indices] also include the variable being eliminated at its head. *)
  let omitted, nb, rev_indices, candidate =
    compute_omitted [] indices [] rev_arity_ctx [] [] 0 in

  (* Now we do a pass backwards to check if we can omit more things. *)
  (* More precisely, for any variable in rev_indices, we can omit it if
   * nothing in the remaining context that was not omitted depends on it. *)
  (* TODO The algorithm is very inefficient for now. *)

  (* ===== BACKWARD PASS ===== *)
  let rec compute_omitted_bis rev_omitted omitted candidate rev_indices nb =
    match omitted, candidate, rev_indices with
    | [], [], [] -> rev_omitted, nb
    | Some rel :: omitted, _ :: candidate, idx :: rev_indices ->
        compute_omitted_bis (Some rel :: rev_omitted) omitted candidate
          rev_indices nb
    | _ :: omitted, None :: candidate, idx :: rev_indices ->
        compute_omitted_bis (None :: rev_omitted) omitted candidate
          rev_indices nb
    | None :: omitted, Some rel :: candidate, idx :: rev_indices ->
        (* We know that [idx] is [Rel rel] and a candidate for omission. *)
        (* TODO Very inefficient... *)
        let new_decl = Context.Rel.Declaration.LocalAssum (anonR, goal) in
        let after = new_decl :: CList.firstn (pred rel) ctx in
        let omit = CList.for_all_i (fun i decl ->
          let decl_ty = Context.Rel.Declaration.get_type decl in
          (* No dependency. *)
          not (Termops.dependent !evd (mkRel (rel - i)) decl_ty) ||
          (* Already omitted. *)
          List.mem (Some i) rev_omitted) 0 after in
        if omit then
          compute_omitted_bis (Some rel :: rev_omitted) omitted candidate
            rev_indices (pred nb)
        else
          compute_omitted_bis (None :: rev_omitted) omitted candidate
            rev_indices nb
    | _, _, _ -> assert false
  in
  let rev_omitted, nb = compute_omitted_bis [] omitted candidate rev_indices nb in
  let omitted = List.rev rev_omitted in

  (* At this point, we have [omitted] which is a list of either [Some rel] when
   * the corresponding index is omitted, [None] otherwise, and [nb] is the number
   * of [None] in this list. *)
  (* Now we consider the context [arity_ctx @ ctx], which is the context of
   * the return type. We will build a context substitution from this context
   * to a new one with shape [cuts @ arity_ctx @ ctx'] where [ctx'] is some
   * sub-context of [ctx], [cuts] is a number of declarations for which we
   * need to introduce cutx, and [arity_ctx] has been left untouched. *)

  (* ===== STRENGTHENING ===== *)
  let subst = Context_map.id_subst (arity_ctx @ ctx) in
  let rev_subst = Context_map.id_subst (arity_ctx @ ctx) in
  let subst, rev_subst = List.fold_left (
    fun (subst, rev_subst) -> function
    | None -> subst, rev_subst
    | Some rel ->
        let ctx = subst.Context_map.src_ctx in
        let fresh_rel = Context_map.mapping_constr !evd subst (EConstr.mkRel 1) in
        let target_rel = EConstr.mkRel (rel + oib.mind_nrealargs + 1) in
        let target_rel = Context_map.mapping_constr !evd subst target_rel in
        let target_rel = EConstr.destRel !evd target_rel in
        let lsubst, lrev_subst = Context_map.new_strengthen env !evd ctx target_rel fresh_rel in
        let res1 = Context_map.compose_subst env ~sigma:!evd lsubst subst in
        let res2 = Context_map.compose_subst env ~sigma:!evd rev_subst lrev_subst in
          res1, res2
  ) (subst, rev_subst) omitted in
  let nb_cuts_omit = pred (EConstr.destRel !evd
   (Context_map.mapping_constr !evd subst (EConstr.mkRel 1))) in
  (* [ctx'] is the context under which we will build the case in a first step. *)
  (* This is [ctx] where everything omitted and cut is removed. *)
  let ctx' = List.skipn (nb_cuts_omit + oib.mind_nrealargs + 1) (rev_subst.Context_map.tgt_ctx) in
  let rev_subst' = List.skipn (nb_cuts_omit + oib.mind_nrealargs + 1) (rev_subst.Context_map.map_inst) in
  let rev_subst' = Context_map.lift_pats (-(oib.mind_nrealargs+1)) rev_subst' in
  let rev_subst_without_cuts = Context_map.mk_ctx_map env !evd ctx rev_subst' ctx' in
  (* Now we will work under a context with [ctx'] as a prefix, so we will be
   * able to go back to [ctx] easily. *)

  (* ===== SUBSTITUTION ===== *)
  let subst = CList.fold_right_i (
    fun i omit subst ->
    match omit with
    | None -> subst
    | Some rel ->
        let ctx = subst.Context_map.src_ctx in
        let pats = subst.Context_map.map_inst in
        let orig = oib.mind_nrealargs + 1 - i in
        let fresh_rel = Context_map.specialize !evd pats (Context_map.PRel orig) in
        let target_rel = EConstr.mkRel (rel + oib.mind_nrealargs + 1) in
        let target_rel = Context_map.mapping_constr !evd subst target_rel in
        let target_rel = EConstr.destRel !evd target_rel in
        (* We know that this call will fall in the simple case
         * of [single_subst], because we already strengthened everything. *)
        (* TODO Related to [compute_omitted_bis], we cannot actually substitute
         * the terms that were omitted simply due to the fact that nothing
         * depends on them, as it would be an ill-typed substitution. *)
        let lsubst = Context_map.single_subst ~unsafe:true env !evd target_rel fresh_rel ctx in
          Context_map.compose_subst ~unsafe:true env ~sigma:!evd lsubst subst
  ) 0 omitted subst in
  let nb_cuts = pred (EConstr.destRel !evd
   (Context_map.mapping_constr !evd subst (EConstr.mkRel 1))) in
  (* Also useful: a substitution from [ctx] to the context with cuts. *)
  let subst_to_cuts =
    let lift_subst = Context_map.mk_ctx_map env !evd (arity_ctx @ ctx)
    (Context_map.lift_pats (oib.mind_nrealargs + 1) (Context_map.id_pats ctx))
    ctx in
      Context_map.compose_subst ~unsafe:true env ~sigma:!evd subst lift_subst
  in

  (* Finally, we can work on producing a return type. *)
  let goal = Context_map.mapping_constr !evd subst_to_cuts goal in

  (* ===== CUTS ===== *)
  let cuts_ctx, remaining = List.chop nb_cuts (subst.Context_map.src_ctx) in
  let fresh_ctx = List.firstn (oib.mind_nrealargs + 1) remaining in
  let revert_cut x =
    let rec revert_cut i = function
      | [] -> failwith "Could not revert a cut, please report."
      | Context_map.PRel y :: _ when Int.equal x y ->
        (match nth cuts_ctx (pred x) with
         | Context.Rel.Declaration.LocalAssum _ -> Some (EConstr.mkRel i)
         | Context.Rel.Declaration.LocalDef _ -> None)
      | _ :: l -> revert_cut (succ i) l
    in revert_cut (- oib.mind_nrealargs) (subst.Context_map.map_inst)
  in
  let rev_cut_vars = CList.map revert_cut (CList.init nb_cuts (fun i -> succ i)) in
  let cut_vars = List.rev rev_cut_vars in
  let cut_vars = CList.map_filter (fun x -> x) cut_vars in

  (* ===== EQUALITY OF TELESCOPES ===== *)
  let goal, to_apply, simpl =
    if Int.equal nb 0 then goal, [], false
    else
      let arity_ctx' = Context_map.specialize_rel_context !evd (subst_to_cuts.Context_map.map_inst) arity_ctx in
      let rev_indices' = List.map (Context_map.mapping_constr !evd subst_to_cuts) rev_indices in
      let _, rev_sigctx, tele_lhs, tele_rhs =
        CList.fold_left3 (
          fun (k, rev_sigctx, tele_lhs, tele_rhs) decl idx -> function
          | Some _ -> (* Don't add a binder, but substitute *)
              let fresh = EConstr.mkRel (nb_cuts + oib.mind_nrealargs + 1) in
              let rev_sigctx = Equations_common.subst_telescope fresh rev_sigctx in
              succ k, rev_sigctx, tele_lhs, tele_rhs
          | None -> (* Add a binder to the telescope. *)
              let rhs = EConstr.mkRel k in
              succ k, decl :: rev_sigctx, idx :: tele_lhs, rhs :: tele_rhs

        ) (succ nb_cuts, [], [], []) arity_ctx' rev_indices' omitted
      in
      let sigctx = List.rev rev_sigctx in
      let sigty, _, sigconstr = telescope (push_rel_context (subst.Context_map.src_ctx) env) evd sigctx in

      (* Build a goal with an equality of telescopes at the front. *)
      let left_sig = Vars.substl (List.rev tele_lhs) sigconstr in
      let right_sig = Vars.substl (List.rev tele_rhs) sigconstr in
      (* TODO Swap left_sig and right_sig... *)
      let eq = Equations_common.mkEq env evd sigty right_sig left_sig in
      let _, equ = EConstr.destInd !evd (fst (destApp !evd eq)) in
      let goal = Vars.lift 1 goal in
      let goal = EConstr.mkProd (anonR, eq, goal) in

      (* Build a reflexivity proof to apply to the case. *)
      let tr_out t =
        let t = it_mkLambda_or_LetIn t cuts_ctx in
        let t = it_mkLambda_or_LetIn t fresh_ctx in
        let t = Context_map.mapping_constr !evd rev_subst_without_cuts t in
          Reductionops.beta_applist !evd (t, indices @ cut_vars)
      in
        goal, [Equations_common.mkRefl ~inst:equ env evd (tr_out sigty) (tr_out left_sig)], true
  in

  (* ===== RESOURCES FOR EACH BRANCH ===== *)
  let params = List.map (Context_map.mapping_constr !evd subst_to_cuts) params in
  (* If something is wrong here, it means that one of the parameters was
   * omitted or cut, which should be wrong... *)
  let params = List.map (Vars.lift (-(nb_cuts + oib.mind_nrealargs + 1))) params in
  let goal = EConstr.it_mkProd_or_LetIn goal cuts_ctx in
  let goal = it_mkLambda_or_LetIn goal fresh_ctx in
  let params = List.map (to_constr ~abort_on_undefined_evars:false !evd) params in
  let goal' = to_constr ~abort_on_undefined_evars:false !evd goal in
  let branches_ty = Inductive.build_branches_type (from_peuniverses !evd pind) (mib, oib) params goal' in
  (* Refresh the inductive family. *)
  let indfam = Inductiveops.make_ind_family (pind, List.map EConstr.of_constr params) in
  let branches_info = Inductiveops.get_constructors env indfam in
  let full_subst =
    let pats = Context_map.id_pats ctx in
    let pats = Context_map.lift_pats (oib.mind_nrealargs + 1) pats in
    let ctx' = arity_ctx @ ctx in
      Context_map.mk_ctx_map env !evd ctx' pats ctx
  in
  let full_subst = Context_map.compose_subst ~unsafe:true env ~sigma:!evd subst full_subst in
  let pats_ctx' = Context_map.id_pats ctx' in
  let pats_cuts = Context_map.id_pats cuts_ctx in
  let branches_subst = Array.map (fun summary ->
    (* This summary is under context [ctx']. *)
    let indices = summary.Inductiveops.cs_concl_realargs in
    let params = Array.of_list summary.Inductiveops.cs_params in
    let term = EConstr.mkConstructU (summary.Inductiveops.cs_cstr) in
    let term = EConstr.mkApp (term, params) in
    let term = Vars.lift (summary.Inductiveops.cs_nargs) term in
    let term = EConstr.mkApp (term, Context.Rel.instance EConstr.mkRel 0 summary.Inductiveops.cs_args) in
    (* Indices are typed under [args @ ctx'] *)
    let indices = (Array.to_list indices) @ [term] in
    let args = summary.Inductiveops.cs_args in
    (* Substitute the indices in [cuts_ctx]. *)
    let rev_indices = List.rev indices in
    let pats_indices = List.map (Context_map.pat_of_constr env !evd) rev_indices in
    let pats_ctx' = Context_map.lift_pats summary.Inductiveops.cs_nargs pats_ctx' in
    let pats = pats_indices @ pats_ctx' in
    let cuts_ctx = Context_map.specialize_rel_context !evd pats cuts_ctx in
    let pats = Context_map.lift_pats nb_cuts pats in
    let pats = pats_cuts @ pats in
    let csubst = Context_map.mk_ctx_map env !evd (cuts_ctx @ args @ ctx') pats (subst.Context_map.src_ctx) in
      Context_map.compose_subst ~unsafe:true env ~sigma:!evd csubst full_subst
  ) branches_info in
  let branches_nb = Array.map (fun summary ->
    summary.Inductiveops.cs_nargs) branches_info in
  let branches_res = Array.map3 (fun x y z -> (of_constr x, y, z))
    branches_ty branches_nb branches_subst in

  (* ===== RESULT ===== *)
  let to_apply = cut_vars @ to_apply in
   (* We have everything we need:
   *  - a context [ctx'];
   *  - a return type [goal] valid under [ctx'];
   *  - the type of the branches of the case;
   *  - the number of arguments of each constructor;
   *  - a context_map for each branch;
   *  - a number of cuts [nb_cuts];
   *  - a reverse substitution [rev_subst_without_cuts] from [ctx] to [ctx'];
   *  - some terms in [ctx] to apply to the case once it is built. *)
      (ctx', goal, branches_res, nb_cuts, rev_subst_without_cuts, to_apply, simpl)


let curry_hyp env sigma hyp t =
  let curry t =
    match kind sigma t with
    | Prod (na, dom, concl) ->
       let ctx, arg = curry env sigma na dom in
       let term = mkApp (mkVar hyp, [| arg |]) in
       let ty = Reductionops.nf_betaiota env sigma (Vars.subst1 arg concl) in
       Some (it_mkLambda_or_LetIn term ctx, it_mkProd_or_LetIn ty ctx)
    | _ -> None
  in curry t

open RedFlags

let red_curry () =
  let redpr pr =
    fPROJ (Projection.repr (Lazy.force pr)) in
  let fold accu r = red_add accu r in
  let reds = mkflags [fDELTA; fBETA; fMATCH] in
  let reds = List.fold_left fold reds [redpr coq_pr1; redpr coq_pr2] in
  Reductionops.clos_norm_flags reds

let curry_concl env sigma na dom codom =
  let ctx, arg = curry env sigma na dom in
  let newconcl =
    let body = it_mkLambda_or_LetIn (Vars.subst1 arg codom) ctx in
    let inst = extended_rel_vect 0 ctx in
    red_curry () env sigma (it_mkProd_or_LetIn (mkApp (body, inst)) ctx) in
  let proj last decl (terms, acc) =
    if last then (acc :: terms, acc)
    else
      (* sigma is not sort poly (at least for now) *)
      let term = mkProj (Lazy.force coq_pr1, ERelevance.relevant, acc) in
      let acc = mkProj (Lazy.force coq_pr2, ERelevance.relevant, acc) in
      (term :: terms, acc)
  in
  let terms, acc =
    match ctx with
    | hd :: (_ :: _ as tl) ->
       proj true hd (List.fold_right (proj false) tl ([], mkRel 1))
    | hd :: tl -> ([mkRel 1], mkRel 1)
    | [] -> ([mkRel 1], mkRel 1)
  in
  let sigma, ev = new_evar env sigma newconcl in
  let term = mkLambda (na, dom, mkApp (ev, CArray.rev_of_list terms)) in
  sigma, term

module Tactics =struct
  open Proofview.Notations
  open Proofview.Goal

  open Tacticals

  let curry_hyp id =
    enter_goal begin fun env sigma _ ->
    let decl = lookup_named id (named_context env) in
    let (na, body, ty) = to_named_tuple decl in
      match curry_hyp env sigma id ty with
      | Some (prf, typ) ->
         (match body with
          | Some b ->
             let newprf = Vars.replace_vars sigma [(id,b)] prf in
             tclTHEN (clear [id]) (Tactics.letin_tac None (Name id) newprf (Some typ) nowhere)
          | None ->
             assert_replacing id prf typ)
      | None -> tclFAIL (str"No currying to do in " ++ Id.print id)
  end

  let curry =
    Proofview.Goal.enter begin fun gl ->
      let env = env gl in
      let sigma = sigma gl in
      let concl = concl gl in
      match kind sigma concl with
      | Prod (na, dom, codom) ->
         Refine.refine ~typecheck:true
           (fun sigma -> curry_concl env sigma na dom codom)
      | _ -> Tacticals.tclFAIL (str"Goal cannot be curried") end

  let uncurry_call c c' id id' =
    enter begin fun gl ->
          let env = env gl in
          let sigma = sigma gl in
          let sigma, term, fterm, ty = uncurry_call env sigma c c' in
          let sigma, _ = Typing.type_of env sigma term in
          Proofview.Unsafe.tclEVARS sigma <*>
            Tactics.letin_tac None (Name id) term (Some ty) nowhere <*>
          Tactics.letin_tac None (Name id') (Vars.subst1 (mkVar id) fterm) None nowhere end

  let get_signature_pack id id' =
    enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      try
        let sigma', sigsig, sigpack =
          get_signature env sigma (Tacmach.pf_get_hyp_typ id gl) in
        Proofview.Unsafe.tclEVARS sigma' <*>
        letin_tac None (Name id') (beta_applist sigma (sigpack, [mkVar id])) None nowhere
      with Not_found ->
        Tacticals.tclFAIL (str"No Signature instance found")
    end

  let pattern_sigma id =
    enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let decl = Tacmach.pf_get_hyp id gl in
    let term = Option.get (get_named_value decl) in
    pattern_sigma ~assoc_right:true term id env sigma end
end
