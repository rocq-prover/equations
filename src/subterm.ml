(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Names
open Nameops
open Constr
open Context
open Termops
open Declarations
open Inductiveops
open Util
open Entries
module CVars = Vars
open EConstr
open Vars

open Equations_common
open Sigma_types

let refresh_universes t = t (* MS: FIXME *)

let derive_subterm ~pm env sigma ~poly (ind, u as indu) =
  let () = 
    if Ederive.check_derive "NoConfusion" (Names.GlobRef.IndRef ind) 
      || Ederive.check_derive "NoConfusionHom" (Names.GlobRef.IndRef ind) then ()
    else 
    user_err_loc (None, Pp.(str "[Derive Subterm] requires a [NoConfusion] " ++
      str"or a [NoConfusionHom] instance for type " ++ Printer.pr_inductive env ind ++ str " to be derived first."))
  in
  let (mind, oneind as ms) = Global.lookup_inductive ind in
  let ctx = CVars.subst_instance_context (EInstance.kind sigma (Inductiveops.get_template_instance mind u)) oneind.mind_arity_ctxt in
  let indsort = 
    let indty = Inductive.type_of_inductive (ms, EInstance.kind sigma u) in
    (snd (Reduction.dest_arity env indty))
  in
  if Sorts.is_prop indsort || Sorts.is_sprop indsort then
    user_err_loc (None, Pp.str("Cannot define a well-founded subterm relation on a propositional inductive type."));
  let sort =
    let open UnivGen.QualityOrSet in
    match Lazy.force logic_sort with
    | Qual (QConstant QSProp) -> failwith "not implemented"
    | Qual (QConstant QProp) -> mkProp
    | Set -> mkSet
    | Qual (QConstant QType | QGlobal _ | QVar _) -> EConstr.mkSort (ESorts.make indsort)
  in
  let len = List.length ctx in
  let params = mind.mind_nparams_rec in
  (* let ctx = map_rel_context refresh_universes ctx in FIXME *)
  let lenargs = len - params in
  let argbinders, parambinders = List.chop lenargs (List.map of_rel_decl ctx) in
  let indapp = mkApp (mkIndU indu, extended_rel_vect 0 parambinders) in
  let getargs t = snd (Array.chop params (snd (decompose_app sigma t))) in
  let inds =
    let branches = Array.mapi (fun i ty ->
      let args, concl = decompose_prod_decls sigma (of_constr ty) in
      let lenargs = List.length args in
      let lenargs' = lenargs - params in
      let args', params' = List.chop lenargs' args in
      let recargs = CList.map_filter_i (fun i decl ->
        let (n, _, t) = to_tuple decl in
        let ctx, ar = decompose_prod_decls sigma t in
          match kind sigma (fst (decompose_app sigma ar)) with
          | Ind (ind',_) when Environ.QInd.equal env ind' ind ->
              Some (ctx, i, mkRel (succ i), getargs (lift (succ i) ar))
          | _ -> None) args'
      in
      let constr = mkApp (mkConstructUi (indu, succ i), extended_rel_vect 0 args) in
      let constrargs = getargs concl in
      let branches = List.map_i
        (fun j (ctx, i', r, rargs) ->
          let ctxlen = List.length ctx in
          let subargs =
            Array.of_list ((extended_rel_list (lenargs' + ctxlen)
                               parambinders)
                            @ Array.to_list rargs @ (Array.map_to_list (lift ctxlen) constrargs) @
                            [mkApp (lift ctxlen r, extended_rel_vect 0 ctx) ;
                             lift ctxlen constr])
          in
          let relapp = mkApp (mkRel (succ lenargs + ctxlen), subargs) in
            (i, j, it_mkProd_or_LetIn (it_mkProd_or_LetIn relapp
                                          (lift_rel_context (succ i') ctx)) args'))
        1 recargs
      in branches) (Inductive.type_of_constructors (from_peuniverses sigma indu) ms)
    in branches
  in
  let branches = Array.fold_right (fun x acc -> x @ acc) inds [] in
  let _trans_branch =
    let liftargbinders = lift_rel_context lenargs argbinders in
    let liftargbinders' = lift_rel_context lenargs liftargbinders in
    let indr = ERelevance.make oneind.mind_relevance in
    let indna id = make_annot (Name (Id.of_string id)) indr in
    let indapp n = (mkApp (lift (3 * lenargs + n) indapp, extended_rel_vect (n + (2 - n) * lenargs) argbinders)) in
    let terms = [(indna "z", None, indapp 2);
                 (indna "y", None, indapp 1);
                 (indna "x", None, indapp 0)]
    in
    let binders = to_context terms @ liftargbinders' @ liftargbinders @ argbinders in
    let lenbinders = 3 * succ lenargs in
    let xy =
      (mkApp (mkRel (succ lenbinders + params),
              Array.of_list
                (extended_rel_list lenbinders parambinders @
                   extended_rel_list (2 * lenargs + 3) argbinders @
                   extended_rel_list (lenargs + 3) argbinders @
                   [mkRel 3; mkRel 2])))
    and yz =
      (mkApp (mkRel (succ lenbinders + params),
              Array.of_list
                (extended_rel_list lenbinders parambinders @
                   extended_rel_list (lenargs + 3) argbinders @
                   extended_rel_list 3 argbinders @
                   [mkRel 2; mkRel 1])))
    and xz =
      (mkApp (mkRel (succ lenbinders + params),
              Array.of_list
                (extended_rel_list lenbinders parambinders @
                   extended_rel_list (2 * lenargs + 3) argbinders @
                   extended_rel_list 3 argbinders @
                   [mkRel 3; mkRel 1])))
    in
      (0, 0,
       it_mkProd_or_LetIn (mkProd (annotR Anonymous, xy, mkProd (annotR Anonymous, lift 1 yz, lift 2 xz))) binders)
  in
  let branches = (* trans_branch ::  *)branches in
  let declare_one_ind i ind branches =
    let indid = Nametab.basename_of_global (Names.GlobRef.IndRef (fst ind)) in
    let subtermid = add_suffix indid "_direct_subterm" in
    let constructors = List.map (fun (i, j, constr) -> EConstr.to_constr sigma constr) branches in
    let consnames = List.map (fun (i, j, _) ->
      add_suffix subtermid ("_" ^ string_of_int i ^ "_" ^ string_of_int j))
      branches
    in
    let lenargs = List.length argbinders in
    let liftedbinders = lift_rel_context lenargs argbinders in
    let binders = liftedbinders @ argbinders in
    let appparams = mkApp (mkIndU ind, extended_rel_vect (2 * lenargs) parambinders) in
    let arity = it_mkProd_or_LetIn
      (mkProd (annotR Anonymous, mkApp (appparams, extended_rel_vect lenargs argbinders),
              mkProd (annotR Anonymous, lift 1 (mkApp (appparams, extended_rel_vect 0 argbinders)),
                      sort)))
      binders
    in
      { mind_entry_typename = subtermid;
        mind_entry_arity = EConstr.to_constr sigma arity;
        mind_entry_consnames = consnames;
        mind_entry_lc = constructors }
  in
  let univs, ubinders = Evd.univ_entry ~poly sigma in
  let uctx = match univs with
  | UState.Monomorphic_entry ctx ->
    let () = Global.push_context_set ctx in
    Entries.Monomorphic_ind_entry
  | UState.Polymorphic_entry uctx -> Entries.Polymorphic_ind_entry uctx
  in
  let declare_ind ~pm =
    let inds = [declare_one_ind 0 indu branches] in
    let inductive =
      { mind_entry_record = None;
        mind_entry_finite = Declarations.Finite;
        mind_entry_params = List.map (fun d -> to_rel_decl sigma (Context.Rel.Declaration.map_constr refresh_universes d)) parambinders;
        mind_entry_inds = inds;
        mind_entry_private = None;
        mind_entry_universes = uctx;
        mind_entry_variance = None;
      }
    in
    let k = DeclareInd.declare_mutual_inductive_with_eliminations inductive (univs, ubinders) [] in
    let () =
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let sigma, ind = Evd.fresh_inductive_instance env sigma (k,0) in
      ignore (Sigma_types.declare_sig_of_ind env sigma ~poly ind) in
    let subind = mkIndU ((k,0), u) in
    let constrhints =
      List.map_i (fun i entry ->
        List.map_i (fun j _ -> empty_hint_info, true,
          GlobRef.ConstructRef ((k,i),j)) 1 entry.mind_entry_lc)
        0 inds
    in
    let locality = if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal in
    let () = Hints.add_hints ~locality [subterm_relation_base]
                             (Hints.HintsResolveEntry (List.concat constrhints)) in
    (* Proof of Well-foundedness *)
    let relid = add_suffix (Nametab.basename_of_global (GlobRef.IndRef ind))
                           "_subterm" in
    let id = add_prefix "well_founded_" relid in
    (* Catch the new signature universe *)
    let env = Global.env () in
    let sigma = Evd.update_sigma_univs (Environ.universes env) sigma in
    let evm = ref sigma in
    let kl = get_efresh logic_wellfounded_class evm in
    let kl = get_class sigma kl in
    let parambinders, body, ty =
      let pars, ty, rel =
        if List.is_empty argbinders then
          (* Standard homogeneous well-founded relation *)
          parambinders, indapp, mkApp (subind, extended_rel_vect 0 parambinders)
        else
          (* Construct a family relation by packaging all indexes into
             a sigma type *)
          let _, _, pars, indices, indexproj, valproj, valsig, typesig =
            sigmaize env evm parambinders indapp in
          let env' = push_rel_context pars env in
          let subrel =
            let liftindices = List.map (liftn 2 2) indices in
            (* sigma is not sort poly (at least for now) *)
            let yindices = List.map (subst1 (mkProj (indexproj, ERelevance.relevant, mkRel 1))) liftindices in
            let xindices = List.map (subst1 (mkProj (indexproj, ERelevance.relevant, mkRel 2))) liftindices in
            let apprel =
              applistc subind (extended_rel_list 2 parambinders @
                                 (xindices @ yindices @
                                    [mkProj (valproj, ERelevance.relevant, mkRel 2); mkProj (valproj, ERelevance.relevant, mkRel 1)]))
            in
            mkLambda (nameR (Id.of_string "x"), typesig,
                      mkLambda (nameR (Id.of_string "y"), lift 1 typesig,
                                apprel))
          in
          let typesig = Tacred.simpl env' !evm typesig in
          let subrel = Tacred.simpl env' !evm subrel in
          pars, typesig, subrel
      in
      let relation =
        let def = it_mkLambda_or_LetIn
                    (mkApp (get_efresh logic_transitive_closure evm, [| ty; rel |]))
                    pars
        in
        let ty = it_mkProd_or_LetIn
            (mkApp (get_efresh logic_relation evm, [| ty |]))
            parambinders
        in
        let kn, (evm', cst) =
          declare_constant relid def (Some ty) ~poly !evm
            ~kind:Decls.(IsDefinition Definition) in
        evm := evm';
        (* Impargs.declare_manual_implicits false (ConstRef cst) ~enriching:false *)
        (* 	(list_map_i (fun i _ -> ExplByPos (i, None), (true, true, true)) 1 parambinders); *)
        Hints.add_hints ~locality [subterm_relation_base]
                        (Hints.HintsUnfoldEntry [Evaluable.EvalConstRef kn]);
        mkApp (cst, extended_rel_vect 0 parambinders)
      in
      let env' = push_rel_context pars env in
      let evar =
        let evt = (mkApp (get_efresh logic_wellfounded evm, [| ty; relation |])) in
        evd_comb1 (Evarutil.new_evar ~typeclass_candidate:false env') evm evt
      in
      let b, t = instance_constructor !evm kl [ ty; relation; evar ] in
      (pars, b, t)
    in
    let ty = it_mkProd_or_LetIn ty parambinders in
    let body = it_mkLambda_or_LetIn (Option.get body) parambinders in
    let hook { Declare.Hook.S.dref; _ } =
      let cst = match dref with GlobRef.ConstRef kn -> kn | _ -> assert false in
      Classes.declare_instance (Global.env ()) !evm (Some empty_hint_info)
                                          Hints.SuperGlobal (GlobRef.ConstRef cst)
    in
    let _bodyty = e_type_of (Global.env ()) evm body in
    let _ty' = e_type_of (Global.env ()) evm ty in
    let evm = Evd.minimize_universes !evm in
    let obls, _, constr, typ = RetrieveObl.retrieve_obligations env id evm 0 body ty in
    let uctx = Evd.ustate evm in
    let cinfo = Declare.CInfo.make ~name:id ~typ () in
    let info = Declare.Info.make ~poly ~scope:Locality.(Global ImportDefaultBehavior)
        ~kind:Decls.(IsDefinition Instance) ~hook:(Declare.Hook.make hook) () in
    let pm = Declare.Obls.add_definition ~pm ~cinfo ~info ~body:constr ~uctx ~opaque:false
                                ~tactic:(solve_subterm_tac ()) obls in
    pm
  in
  declare_ind ~pm

let () =
  Ederive.(register_derive
            { derive_name = "Subterm";
              derive_fn = make_derive_ind derive_subterm })

let derive_below env sigma ~poly (ind,univ as indu) =
  let evd = ref sigma in
  let mind, oneind = Global.lookup_inductive ind in
  let univ = Inductiveops.get_template_instance mind univ in
  let ctx = oneind.mind_arity_ctxt in
  let params = mind.mind_nparams in
  let realargs = oneind.mind_nrealargs in
  let realdecls = oneind.mind_nrealdecls in
  let ctx = List.map of_rel_decl ctx in
  let allargsvect = extended_rel_vect 0 ctx in
  let indty = mkApp (mkIndU indu, allargsvect) in
  let indr = ERelevance.make oneind.mind_relevance in
  let ctx = of_tuple (make_annot (Name (Id.of_string "c")) indr, None, indty) :: ctx in
  let argbinders, parambinders = List.chop (succ realdecls) ctx in
  let u = evd_comb0 (Evd.new_sort_variable Evd.univ_rigid) evd in
  let ru = Retyping.relevance_of_sort u in
  let u = mkSort u in
  let arity = it_mkProd_or_LetIn u argbinders in
  let aritylam = lift (succ realdecls) (it_mkLambda_or_LetIn u argbinders) in
  let paramsvect = rel_vect (succ realdecls) params in
  let argsvect = extended_rel_vect 0 (CList.firstn (succ realdecls) ctx) in
  let pid = Id.of_string "P" in
  let pdecl = make_assum (make_annot (Name pid) ru) arity in
  let arity = lift 1 arity in
  let stepid = Id.of_string "step" in
  let recid = Id.of_string "rec" in
  let belowid = Id.of_string "below" in
  let paramspargs = Array.append (Array.append paramsvect [| mkVar pid |]) argsvect in
  let tyb = mkApp (mkVar belowid, paramspargs) in
  let arityb = lift 2 (it_mkProd_or_LetIn tyb argbinders) in
  let aritylamb = lift (succ realdecls) (it_mkLambda_or_LetIn tyb argbinders) in
  let termB, termb = 
    let branches = Array.mapi (fun i (ctx, ty) ->
      let ty = Term.it_mkProd_or_LetIn ty ctx in
      let ty = of_constr ty in
      let ty = Vars.subst_instance_constr univ ty in
      let nargs = constructor_nrealargs env (ind, succ i) in
      let recarg = mkVar recid in
      let args, _ = decompose_prod_decls !evd ty in
      let args, _ = List.chop (List.length args - params) args in
      let ty' = replace_term !evd (mkApp (mkIndU indu, rel_vect (-params) params)) recarg ty in
      let args', _ = decompose_prod_decls !evd ty' in
      let args', _ = List.chop (List.length args' - params) args' in
      let arg_tys = fst (List.fold_left (fun (acc, n) decl ->
        let t = get_type decl in
	((mkRel n, lift n t) :: acc, succ n)) ([], 1) args')
      in
      let fold_unit f args =
	let res = 
	  List.fold_left (fun acc x ->
	    match acc with
	    | Some (c, ty) -> Option.cata (fun x -> Some x) acc (f (fun (c', ty') ->
                mkApp (get_efresh logic_pair evd, [| ty' ; ty ; c' ; c |]),
                mkApp (get_efresh logic_product evd, [| ty' ; ty |])) x)
	    | None -> f (fun x -> x) x)
	    None args
	in Option.cata (fun x -> x)
                       (get_efresh logic_unit_intro evd,
                        get_efresh logic_unit evd) res
      in
      (* This wrapper checks if the argument is a recursive one,
       * and do the appropriate transformations if it is a product. *)
      let wrapper f = fun g (c, t) ->
        let prem, res = decompose_prod_decls !evd t in
        let t, args = decompose_app !evd res in
          if eq_constr !evd t recarg then
            let nprem = List.length prem in
            let elt = mkApp (lift nprem c, rel_vect 0 nprem) in
            let args = Array.append args [| elt |] in
            let res, ty = f args nprem in
            let res = it_mkLambda_or_LetIn res prem in
            let ty = it_mkProd_or_LetIn ty prem in
              Some (g (res, ty))
          else None in
      let prod = get_efresh logic_product evd in
      let _, bodyB = fold_unit (wrapper (fun args _ ->
        let ty = mkApp (prod,
          [| mkApp (mkVar pid, args) ;
             mkApp (mkVar recid, args) |]) in
          mkRel 0, ty)) arg_tys in
      let bodyb, _ = fold_unit (wrapper (fun args nprem ->
        let reccall = mkApp (mkVar recid, args) in
        let belowargs = Array.append (rel_vect (nargs + nprem) params)
          (Array.append [| mkVar pid |] args) in
        let res = mkApp (get_efresh logic_pair evd,
                         [| mkApp (mkVar pid, args) ;
                            mkApp (mkVar belowid, belowargs) ;
                            mkApp (mkApp (mkVar stepid, args), [| reccall |]);
                            reccall |]) in
        let ty = mkApp (prod,
                       [| mkApp (mkVar pid, args) ;
                          mkApp (mkVar belowid, belowargs) |]) in
        res, ty)) arg_tys in
      (* The free variables correspond to the inductive parameters. *)
      let bodyB = lift (succ realdecls) (it_mkLambda_or_LetIn bodyB args) in
      let bodyb = lift (succ realdecls) (it_mkLambda_or_LetIn bodyb args) in
        (nargs, bodyB, bodyb)) oneind.mind_nf_lc
    in
    let caseB =
      mkCase (EConstr.contract_case env !evd (make_case_info env ind MatchStyle, (aritylam, ERelevance.relevant), NoInvert, mkRel 1, Array.map pi2 branches))
    and caseb =
      mkCase (EConstr.contract_case env !evd (make_case_info env ind MatchStyle, (aritylamb, ERelevance.relevant), NoInvert, mkRel 1, Array.map pi3 branches))
    in 
      lift 2 (it_mkLambda_or_LetIn caseB argbinders), lift 3 (it_mkLambda_or_LetIn caseb argbinders)
  in
  let fixB = mkFix (([| realargs |], 0), ([| make_annot (Name recid) ru |], [| arity |],
				     [| subst_vars !evd [recid; pid] termB |])) in
  let bodyB = it_mkLambda_or_LetIn fixB (pdecl :: parambinders) in
  let id = add_prefix "Below_" (Nametab.basename_of_global (GlobRef.IndRef ind)) in
  let _, (evd, belowB) = declare_constant id bodyB None ~poly !evd
      ~kind:Decls.(IsDefinition Definition) in
  let fixb = mkFix (([| realargs |], 0), ([| nameR recid |], [| arityb |],
				    [| subst_vars evd [recid; stepid] termb |])) in
  let stepdecl =
    let stepty = mkProd (anonR, mkApp (belowB, paramspargs),
                        mkApp (mkVar pid, Array.map (lift 1) argsvect))
    in make_assum (nameR stepid) (lift 1 (it_mkProd_or_LetIn stepty argbinders))
  in
  let bodyb = 
    it_mkLambda_or_LetIn
      (subst_vars evd [pid] (mkLambda_or_LetIn stepdecl fixb))
      (pdecl :: parambinders)
  in
  let bodyb = replace_vars evd [belowid, belowB] bodyb in
  let bodyb = Evarutil.nf_evar evd bodyb in
  let id = add_prefix "below_" (Nametab.basename_of_global (GlobRef.IndRef ind)) in
  let evd = if PolyFlags.univ_poly poly then evd else Evd.from_env (Global.env ()) in
  ignore(declare_constant id bodyb None ~poly evd
	   ~kind:Decls.(IsDefinition Definition))

let () =
  let derive_below ~pm env sigma ~poly indu =
    let () = derive_below env sigma ~poly indu in pm
  in
  Ederive.(register_derive
            { derive_name = "Below";
              derive_fn = make_derive_ind derive_below })
