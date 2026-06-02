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
open Declarations
open Inductiveops
open Reductionops
module CVars = Vars
open Equations_common
open EConstr
open Vars

let mkcase env sigma c ty constrs =
  let cty = Retyping.get_type_of env sigma c in
  let IndType (indf, _) as indty = Inductiveops.find_rectype env sigma cty in
  let mind, ind, origparams = match dest_ind_family indf with
    | (((mu, n),_ as i), pars) -> mu, i, pars
  in
  let mindb, oneind = Global.lookup_inductive (fst ind) in
  let ctx = oneind.mind_arity_ctxt in
  let ui = Inductiveops.get_template_instance mindb (snd ind) in
  let ui = EConstr.EInstance.kind sigma ui in
  let ctx = CVars.subst_instance_context ui ctx in
  let _len = List.length ctx in
  let params = mindb.mind_nparams in
  let ci = make_case_info env (fst ind) MatchStyle in
  let brs = 
    Array.map2_i (fun i id (ctx, cty) ->
      let cty = Term.it_mkProd_or_LetIn cty ctx in
      let cty = CVars.subst_instance_constr ui cty in
      let (args, arity) = decompose_prod_decls sigma (of_constr cty) in
      let realargs, pars = List.chop (List.length args - params) args in
      let args = substl (List.rev origparams) (it_mkProd_or_LetIn arity realargs) in
      let args, arity = decompose_prod_decls sigma args in
      let res = constrs ind i id params args arity in
      it_mkLambda_or_LetIn res args)
      oneind.mind_consnames oneind.mind_nf_lc
  in
    make_case_or_project env sigma indty ci (ty, ERelevance.relevant) c brs

let mk_eq env env' evd args args' =
  let _, _, make = Sigma_types.telescope env evd args in
  let _, _, make' = Sigma_types.telescope env' evd args' in
  let make = lift (List.length args + 1) make in
  let env = push_rel_context args' env' in
  let ty = Retyping.get_type_of env !evd make in
  mkEq env evd ty make make'

let derive_no_confusion ~pm env sigma0 ~poly (ind,u as indu) =
  let evd = ref sigma0 in
  let mindb, oneind = Global.lookup_inductive ind in
  let _, inds = Reductionops.dest_arity env sigma0 (Inductiveops.type_of_inductive env indu) in
  let ctx = List.map of_rel_decl oneind.mind_arity_ctxt in
  let u = Inductiveops.get_template_instance mindb u in
  let ctx = subst_instance_context u ctx in
  let ctx = smash_rel_context ctx in
  let len = List.length ctx in
  let params = mindb.mind_nparams in
  let args = oneind.mind_nrealargs in
  let argsvect = rel_vect 0 len in
  let paramsvect, rest = Array.chop params argsvect in
  let argr, argty, x, ctx, argsctx =
    if Array.length rest = 0 then
      ERelevance.make oneind.mind_relevance, mkApp (mkIndU indu, argsvect), mkRel 1, ctx, []
    else
      let evm, pred, pars, indty, valsig, ctx, lenargs, idx =
        Sigma_types.build_sig_of_ind env !evd indu
      in
      let () = evd := evm in
      let evm, sigma = Evd.fresh_global (Global.env ()) !evd (Lazy.force coq_sigma) in
      let () = evd := evm in
      let _, pred' = Term.decompose_lambda_n (List.length pars) (EConstr.to_constr !evd pred) in
      let indty = mkApp (sigma, [|idx; of_constr pred'|]) in
      (* sigma is not sort poly (at least for now) *)
      ERelevance.relevant, nf_betaiotazeta env !evd indty, mkProj (Lazy.force coq_pr2, ERelevance.relevant, mkRel 1), pars, (List.firstn lenargs ctx)
  in
  let tru = get_efresh logic_top evd in
  let fls = get_efresh logic_bot evd in
  let xid = Id.of_string "x" and yid = Id.of_string "y" in
  let xdecl = of_tuple (make_annot (Name xid) argr, None, argty) in
  let binders = xdecl :: ctx in
  let ydecl = of_tuple (make_annot (Name yid) argr, None, lift 1 argty) in
  let fullbinders = ydecl :: binders in
  let s = Lazy.force logic_sort in
  let s =
    let open UnivGen.QualityOrSet in
    match s with
    | Qual (QConstant QSProp) -> mkSProp
    | Qual (QConstant QProp) -> mkProp
    | Set -> mkSet
    | Qual (QConstant QType | QVar _ | QGlobal _) ->
      (* In that case the noConfusion principle lives at the level of the type. *)
      let sort = EConstr.mkSort inds in
      let sigma, s =
        Evarsolve.refresh_universes ~status:Evd.univ_flexible ~onlyalg:true
          (Some false) env !evd sort
      in evd := sigma; s
  in
  let arity = it_mkProd_or_LetIn s fullbinders in
  let env = push_rel_context binders env in
  let paramsvect = Context.Rel.instance mkRel 0 ctx in
  let pack_ind_with_parlift n = lift n argty in
  let ind_with_parlift n = 
    mkApp (mkIndU indu, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let lenindices = List.length argsctx in
  let pred =
    let elim =
      (* In pars ; x |- fun args (x : ind pars args) => forall y, Prop *)
      let app = pack_ind_with_parlift (args + 2) in
	      it_mkLambda_or_LetIn 
          (mkProd_or_LetIn (of_tuple (make_annot Anonymous argr, None, app)) s)
          (of_tuple (nameR xid, None, ind_with_parlift (lenindices + 1)) ::
             lift_rel_context 1 argsctx)
    in
      mkcase env !evd x elim (fun ind i id nparams args arity ->
        let ydecl = (nameR yid, None, pack_ind_with_parlift (List.length args + 1)) in
        let env' = push_rel_context (of_tuple ydecl :: args) env in
        let argsctx = lift_rel_context (List.length args + 2) argsctx in
        let elimdecl = (nameR yid, None, ind_with_parlift (List.length args + lenindices + 2)) in
	        mkLambda_or_LetIn (of_tuple ydecl)
            (mkcase env' !evd x
	        (it_mkLambda_or_LetIn s (of_tuple elimdecl :: argsctx))
	        (fun _ i' id' nparams args' arity' ->
	          if i = i' then
	            if List.length args = 0 then tru
                    else mk_eq env env' evd args args'
	          else fls)))
  in
  let app = it_mkLambda_or_LetIn pred binders in
  let _, ce = make_definition ~poly !evd ~types:arity app in
  let indid = Nametab.basename_of_global (GlobRef.IndRef ind) in
  let id = add_prefix "NoConfusion_" indid in
  let cstNoConf = Declare.declare_constant ~name:id (Declare.DefinitionEntry ce) ~kind:Decls.(IsDefinition Definition) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, indu = Evd.fresh_global
      ~rigid:Evd.univ_rigid (* Universe levels of the inductive family should not be tampered with. *)
      env sigma (GlobRef.IndRef ind) in
  let indu = destInd sigma indu in
  Noconf_hom.derive_noConfusion_package ~pm env sigma ~poly indu indid
    ~prefix:"" ~tactic:(noconf_tac ()) cstNoConf

let () =
  Ederive.(register_derive
            { derive_name = "NoConfusion";
              derive_fn = make_derive_ind derive_no_confusion })
