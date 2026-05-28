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
open Equations_common
open EConstr
open Vars

let name_context env sigma ctx =
  let avoid, ctx =
    List.fold_right (fun decl (avoid, acc) ->
      let (n, b, t) = to_tuple decl in
      match n.binder_name with
      | Name id -> let id' = Namegen.next_ident_away id avoid in
        let avoid = Id.Set.add id' avoid in
        (avoid, make_def (nameR id') b t :: acc)
      | Anonymous ->
        let id' = Namegen.id_of_name_using_hdchar
            (push_rel_context acc env) sigma t Anonymous in
        let avoid = Id.Set.add id' avoid in
        (avoid, make_def (nameR id') b t :: acc))
      ctx (Id.Set.empty, [])
  in ctx

let occur_rigidly sigma i concl =
  let rec aux concl =
    match kind sigma concl with
    | App (f, cl) ->
      if isConstruct sigma f then
        Array.exists aux cl
      else false
    | Rel k -> Int.equal k i
    | _ -> false
  in
  let hd, args = decompose_appvect sigma concl in
  Array.exists aux args

(* On [xn :: ... x1] returns [forcedn :: .. :: forced1] *)
let get_forced_positions sigma args concl =
  let is_forced i acc _ =
    if occur_rigidly sigma i concl then true :: acc
    else false :: acc
  in
  List.rev (List.fold_left_i is_forced 1 [] args)

let derive_noConfusion_package ~pm env sigma ~poly (ind, u) indid ~prefix ~tactic cstNoConf =
  let mindb, oneind = Global.lookup_inductive ind in
  let ctx = List.map of_rel_decl oneind.mind_arity_ctxt in
  let u = Inductiveops.get_template_instance mindb u in
  let ctx = subst_instance_context u ctx in
  let ctx = smash_rel_context ctx in
  let len =
    if prefix = "" then mindb.mind_nparams
    else List.length ctx in
  let argsvect = rel_vect 0 len in
  let noid = add_prefix "noConfusion" (add_prefix prefix (add_prefix "_" indid))
  and packid = add_prefix "NoConfusion" (add_prefix prefix (add_prefix "Package_" indid)) in
  let tc = Typeclasses.class_info_exn env sigma (Lazy.force coq_noconfusion_class) in
  let sigma, noconf = Evd.fresh_global ~rigid:Evd.univ_rigid env sigma (GlobRef.ConstRef cstNoConf) in
  let sigma, noconfcl = new_global sigma tc.Typeclasses.cl_impl in
  let inst, u = destInd sigma noconfcl in
  let noconfterm = mkApp (noconf, argsvect) in
  let ctx, argty =
    let ty = Retyping.get_type_of env sigma noconf in
    let ctx, ty = EConstr.decompose_prod_n_decls sigma len ty in
    match kind sigma ty with
    | Prod (_, b, _) -> ctx, b
    | _ -> assert false
  in
  let b, ty =
    Equations_common.instance_constructor sigma (tc,u) [argty; noconfterm]
  in
  let env = push_rel_context ctx (Global.env ()) in
  let rec term sigma c ty =
    match kind sigma ty with
    | Prod (na, t, ty) ->
       let sigma, arg = Evarutil.new_evar ~typeclass_candidate:true env sigma t in
       term sigma (mkApp (c, [|arg|])) (subst1 arg ty)
    | _ -> sigma, c, ty
  in
  let cty = Retyping.get_type_of env sigma (Option.get b) in
  let sigma, term, ty = term sigma (Option.get b) cty in
  let term = it_mkLambda_or_LetIn term ctx in
  let ty = it_mkProd_or_LetIn ty ctx in
  let sigma, _ = Typing.type_of env sigma term in
  let hook { Declare.Hook.S.dref; _ } =
    Classes.declare_instance (Global.env ()) sigma
      (Some empty_hint_info) Hints.SuperGlobal dref
  in
  let hook = Declare.Hook.make hook in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let kind = Decls.(IsDefinition Definition) in
  let oblinfo, _, term, ty = RetrieveObl.retrieve_obligations env noid sigma 0 term ty in
  let cinfo = Declare.CInfo.make ~name:packid ~typ:ty () in
  let info = Declare.Info.make ~hook ~poly ~scope ~kind () in
  let pm = Declare.Obls.add_definition ~pm ~cinfo ~info ~opaque:false
             ~body:term ~tactic ~uctx:(Evd.ustate sigma) oblinfo in
  pm

let derive_no_confusion_hom ~pm env sigma0 ~poly (ind,u as indu) =
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
  let argty, x, ctx, argsctx =
    mkApp (mkIndU indu, argsvect), mkRel 1, ctx, []
  in
  let sigma, tru = get_fresh sigma0 logic_top in
  let sigma, fls = get_fresh sigma logic_bot in
  let ctx = name_context env sigma ctx in
  let xid = Id.of_string "x" and yid = Id.of_string "y" in
  let xdecl = of_tuple (nameR xid, None, argty) in
  let binders = xdecl :: ctx in
  let ydecl = of_tuple (nameR yid, None, lift 1 argty) in
  let fullbinders = ydecl :: binders in
  let sigma, s =
    let open UnivGen.QualityOrSet in
    match Lazy.force logic_sort with
    | Qual (QConstant QType | QVar _) | Set -> (* In that case noConfusion lives at the level of the inductive family *)
      let sort = EConstr.mkSort inds in
      let is_level = Univ.Universe.is_level (Sorts.univ_of_sort @@ ESorts.kind sigma0 inds) in
      if is_level then sigma, sort
      else
        Evarsolve.refresh_universes ~status:Evd.univ_flexible ~onlyalg:true
          (Some false) env sigma sort
    | s -> let sigma, s = Evd.fresh_sort_in_quality sigma s in
      sigma, mkSort s
  in
  let _arity = it_mkProd_or_LetIn s fullbinders in
  (* let env = push_rel_context binders env in *)
  let paramsvect = Context.Rel.instance mkRel 0 ctx in
  let _pack_ind_with_parlift n = lift n argty in
  let _ind_with_parlift n =
    mkApp (mkIndU indu, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let _lenindices = List.length argsctx in
  let ctxmap = Context_map.id_subst fullbinders in
  let constructors = Inductiveops.arities_of_constructors env indu in
  let sigma, sigT = get_fresh sigma coq_sigma in
  let sigma, sigI = get_fresh sigma coq_sigmaI in
  let sigma, eqT = get_fresh sigma logic_eq_type in
  let parampats =
    List.rev_map (fun decl ->
        DAst.make Syntax.(PUVar (Name.get_id (get_name decl), Generated))) ctx
  in
  let mk_clause i ty =
    let paramsctx, concl = decompose_prod_n_decls sigma params ty in
    let _, ctxpars = List.chop args ctx in
    let ctxvars = List.map (fun decl -> mkVar (Name.get_id (get_name decl))) ctxpars in
    let args, concl = decompose_prod_decls sigma (Vars.substnl ctxvars 0 concl) in
    let forced = get_forced_positions sigma args concl in
    let loc = None in
    let fn (avoid, acc) decl forced =
      let id = match Context.Rel.Declaration.get_name decl with
        | Name na -> na
        | Anonymous -> Id.of_string "wildcard"
      in
      let name = Namegen.next_ident_away (add_suffix id "0") avoid in
      let avoid = Id.Set.add name avoid in
      let name' = Namegen.next_ident_away (add_suffix id "1") avoid in
      let avoid = Id.Set.add name' avoid in
      let acc =
        if forced then
          let acc' =
            List.fold_left_i
              (fun i acc (na,na',decl) -> (na, na', Vars.substnl [mkVar name'] i decl) :: acc)
              0 [] acc
          in List.rev acc'
        else ((name, name', get_type decl) :: acc) in
      (avoid, acc), Syntax.(PUVar (name, User), PUVar (name', User))
    in
    let (avoid, eqs), user_pats = List.fold_left2_map fn (Id.Set.empty, []) args forced in
    let patl, patr = List.split user_pats in
    let cstr ps = Syntax.PUCstr ((ind, succ i), params, List.rev_map (fun p -> DAst.make p) ps) in
    let lhs = parampats @ [DAst.make (cstr patl); DAst.make (cstr patr)] in
    let rhs =
      match List.rev eqs with
      | [] -> tru
      | (name, name', ty) :: eqs ->
        let ty, lhs, rhs =
          let get_type (restty, restl, restr) (na, na', ty) =
            let codom = mkLambda (nameR na, ty, restty) in
            mkApp (sigT, [| ty; codom |]),
            mkApp (sigI, [| ty; codom; mkVar na; subst1 (mkVar na) restl |]),
            mkApp (sigI, [| ty; codom; mkVar na'; subst1 (mkVar na') restr |])
          in
          List.fold_left get_type (ty, mkVar name, mkVar name') eqs
        in mkApp (eqT, [| ty; lhs; rhs |])
    in
    Syntax.Pre_clause (loc, lhs, Some (Syntax.Program (Syntax.Constr rhs, ([], []))))
  in
  let clauses = Array.to_list (Array.mapi mk_clause constructors) in
  let hole x = Syntax.(PUVar (Id.of_string x, User)) in
  let catch_all =
    let lhs = parampats @ [DAst.make (hole "x"); DAst.make (hole "y")] in
    let rhs = Syntax.Program (Syntax.Constr fls, ([], [])) in
    Syntax.Pre_clause (None, lhs, Some rhs)
  in
  let clauses = clauses @ [catch_all] in
  let indid = Nametab.basename_of_global (GlobRef.IndRef ind) in
  let id = add_prefix "NoConfusionHom_" indid in
  let program_orig_type = it_mkProd_or_LetIn s fullbinders in
  let program_sort = Retyping.get_sort_of env sigma program_orig_type in
  let sigma, program_sort =
    Evarsolve.refresh_universes ~status:Evd.univ_flexible ~onlyalg:true
      (Some false) env sigma (mkSort program_sort) in
  let program_sort = EConstr.ESorts.kind sigma (EConstr.destSort sigma program_sort) in
  let evd = ref sigma in
  let data =
    Covering.{
      program_mode = false;
      rec_type = [None];
      flags = { poly = poly; obligations = false; open_proof = false;
                with_eqns = false; with_ind = false; 
                allow_aliases = true; (* We let the compiler unify arguments that are forced equal *)
                tactic = !Declare.Obls.default_tactic };
      fixdecls = [];
      intenv = Constrintern.empty_internalization_env;
      notations = []
    }
  in
  let p = Syntax.{program_loc = None;
                  program_id = id;
                  program_impls = []; program_implicits = [];
                  program_rec = None;
                  program_orig_type;
                  program_sort;
                  program_sign = fullbinders;
                  program_arity = s}
  in
  let splitting =
    Covering.covering ~check_unused:false (* The catch-all clause might not be needed *)
      env evd p data clauses [] ctxmap [] s in
  let hook ~pm _ p terminfo =
    (* let _proginfo =
     *   Syntax.{ program_loc = None; program_id = id;
     *            program_orig_type; program_sort;
     *            program_sign = fullbinders;
     *            program_arity = s;
     *            program_rec = None;
     *            program_impls = [];
     *            program_implicits = []}
     * in *)
    let program_cst = match terminfo.Splitting.term_id with GlobRef.ConstRef c -> c | _ -> assert false in
    (* let _compiled_info = Splitting.{ program_cst; program_split = p.program_splitting;
     *                                 program_split_info = terminfo } in
     * let _flags = { polymorphic; open_proof = false; with_eqns = true; with_ind = true } in
     * let _fixprots = [s] in *)
    (* let () = Equations.define_principles flags None fixprots [proginfo, compiled_info] in *)
    (* The principles are now shown, let's prove this forms an equivalence *)
    Global.set_strategy (Conv_oracle.EvalConstRef program_cst) Conv_oracle.transparent;
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, indu = Evd.fresh_global
        ~rigid:Evd.univ_rigid (* Universe levels of the inductive family should not be tampered with. *)
        env sigma (GlobRef.IndRef ind) in
    let indu = destInd sigma indu in
    (), derive_noConfusion_package ~pm env sigma ~poly indu indid
      ~prefix:"Hom" ~tactic:(noconf_hom_tac ()) program_cst
 in
 let prog = Splitting.make_single_program env evd data.Covering.flags p ctxmap splitting None in
 Splitting.define_programs ~pm env evd UState.default_univ_decl [None] [] data.Covering.flags [prog] hook

let () =
  let derive_no_confusion_hom ~pm env sigma ~poly v =
    derive_no_confusion_hom ~pm env sigma ~poly v |> fst
  in
  Ederive.(register_derive
             { derive_name = "NoConfusionHom";
               derive_fn = make_derive_ind derive_no_confusion_hom })
