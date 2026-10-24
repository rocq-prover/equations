(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

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
open Namegen
open Tactics

open EConstr
open Equations_common
open Vars

let hyps_of_vars env sigma sign nogen hyps =
  if Id.Set.is_empty hyps then []
  else
    let (_,lh) =
      fold_named_context_reverse
        (fun (hs,hl) decl ->
           let x = get_id decl in
          if Id.Set.mem x nogen then (hs,hl)
          else if Id.Set.mem x hs then (hs,x::hl)
          else
            let xvars = global_vars_set_of_decl env sigma decl in
              if not (Id.Set.equal (Id.Set.diff xvars hs) Id.Set.empty) then
                (Id.Set.add x hs, x :: hl)
              else (hs, hl))
        ~init:(hyps,[])
        sign
    in lh

exception Seen

let linear sigma vars args =
  let seen = ref vars in
    try
      Array.iter (fun i ->
        let rels = ids_of_constr ~all:true sigma Id.Set.empty i in
        let seen' =
          Id.Set.fold (fun id acc ->
            if Id.Set.mem id acc then raise Seen
            else Id.Set.add id acc)
            rels !seen
        in seen := seen')
        args;
      true
    with Seen -> false


let needs_generalization gl id =
  let open Tacmach in
  let open Proofview.Goal in
  let env = env gl in
  let sigma = sigma gl in
  let f, args, def, id, oldid =
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = to_named_tuple (pf_get_hyp id gl) in
      match b with
      | None -> let f, args = decompose_app sigma t in
                  f, args, false, id, oldid
      | Some t ->
          let f, args = decompose_app sigma t in
            f, args, true, id, oldid
  in
    if Array.is_empty args then false
    else
      let f', args' = decompose_indapp sigma f args in
      let parvars = ids_of_constr ~all:true sigma Id.Set.empty f' in
        if not (linear sigma parvars args') then true
        else Array.exists (fun x -> not (isVar sigma x) || is_section_variable_env env (destVar sigma x)) args'


let dependent_pattern ?(pattern_term=true) c =
  enter_goal (fun env sigma concl ->
  let cr = Retyping.relevance_of_term env sigma c in
  let cty = Retyping.get_type_of env sigma c in
  let deps =
    match kind sigma cty with
    | App (f, args) ->
        let f', args' = decompose_indapp sigma f args in
          Array.to_list args'
    | _ -> []
  in
  let varname c = match kind sigma c with
    | Var id -> id
    | _ -> next_ident_away (Id.of_string (hdchar env sigma c))
             (Id.Set.of_list (ids_of_named_context (named_context env)))
  in
  let mklambda (ty, sigma) (c, id, r, cty) =
    let conclvar, sigma =
      Find_subterm.subst_closed_term_occ env sigma
        (Locus.AtOccs Locus.AllOccurrences) c ty
    in
      mkNamedLambda sigma (make_annot id r) cty conclvar, sigma
  in
  let subst =
    let map c = (c, varname c, Retyping.relevance_of_term env sigma c, Retyping.get_type_of env sigma c) in
    let deps = List.rev_map map deps in
    if pattern_term then (c, varname c, cr, cty) :: deps
    else deps
  in
  let concllda, evd = List.fold_left mklambda (concl, sigma) subst in
  let conclapp = applistc concllda (List.rev_map (fun (c, _, _, _) -> c) subst) in
    convert_concl ~cast:false ~check:false conclapp DEFAULTcast)

let annot_of_context ctx =
  Array.map_of_list Context.Rel.Declaration.get_annot (List.rev ctx)

let depcase ~poly ((mind, i as ind), u) =
  let indid = Nametab.basename_of_global (GlobRef.IndRef ind) in
  let mindb, oneind = Global.lookup_inductive ind in
  let relevance = ERelevance.make oneind.mind_relevance in
  let indna x = make_annot x relevance in
  let ctx = oneind.mind_arity_ctxt in
  let nparams = mindb.mind_nparams in
  let ctx = List.map of_rel_decl ctx in
  let args, params = List.chop (List.length ctx - nparams) ctx in
  let nargs = List.length args in
  let indapp = mkApp (mkIndU (ind,u), extended_rel_vect 0 ctx) in
  let evd = ref (Evd.from_env (Global.env())) in
  let s = evd_comb0 (Evd.new_sort_variable Evd.univ_flexible) evd in
  let pred = it_mkProd_or_LetIn (mkSort s)
    (make_assum (indna Anonymous) indapp :: args)
  in
  let nconstrs = Array.length oneind.mind_nf_lc in
  let mkbody i (ctx, ty) =
    let args = Context.Rel.instance mkRel 0 ctx in
    annot_of_context (EConstr.of_rel_context ctx), mkApp (mkRel (1 + nconstrs + List.length ctx - i), args)
  in
  let bodies = Array.mapi mkbody oneind.mind_nf_lc in
  let branches =
    Array.map2_i (fun i id (ctx, cty) ->
      let cty = Term.it_mkProd_or_LetIn cty ctx in
      let substcty = Vars.subst_instance_constr u (of_constr cty) in
      let (args, arity) = decompose_prod_decls !evd substcty in
      let _, indices = decompose_app !evd arity in
      let _, indices = Array.chop nparams indices in
      let ncargs = List.length args - nparams in
      let realargs, pars = List.chop ncargs args in
      let realargs = lift_rel_context (i + 1) realargs in
      let arity = applistc (mkRel (ncargs + i + 1))
        (Array.to_list indices @ [mkApp (mkConstructU ((ind, succ i), u),
                          Array.append (extended_rel_vect (ncargs + i + 1) params)
                            (extended_rel_vect 0 realargs))])
      in
      let br = it_mkProd_or_LetIn arity realargs in
        (make_assum (nameR (Id.of_string ("P" ^ string_of_int i))) br))
      oneind.mind_consnames oneind.mind_nf_lc
  in
  let ci = make_case_info (Global.env ()) ind MatchStyle in
  let obj i =
    mkApp (mkIndU (ind,u),
          (Array.append (extended_rel_vect (nargs + nconstrs + i) params)
              (extended_rel_vect 0 args)))
  in
  let ctxpred = make_assum (indna Anonymous) (obj (2 + nargs)) :: args in
  let app = mkApp (mkRel (nargs + nconstrs + 3),
                  (extended_rel_vect 0 ctxpred))
  in
  let paramsinst = extended_rel_vect (2 + nargs + nconstrs) params in
  let ty = (annot_of_context ctxpred, app) in
  let case = mkCase (ci, EInstance.empty, paramsinst, (ty, relevance), NoInvert, mkRel 1, bodies) in
  let xty = obj 1 in
  let xid = Namegen.named_hd (Global.env ()) !evd xty Anonymous in
  let body =
    let len = 1 (* P *) + Array.length branches in
    it_mkLambda_or_LetIn case
      (make_assum (indna xid) (lift len indapp)
        :: ((Array.rev_to_list branches)
            @ (make_assum (make_annot (Name (Id.of_string "P")) (Retyping.relevance_of_sort s)) pred :: ctx)))
  in
  let () = evd := Evd.minimize_universes !evd in
  let univs = Evd.univ_entry ~poly !evd in
  let ce = Declare.definition_entry ~univs (EConstr.to_constr !evd body) in
  let kn =
    let id = add_suffix indid "_dep_elim" in
      GlobRef.ConstRef (Declare.declare_constant ~name:id
                  (Declare.DefinitionEntry ce) ~kind:Decls.(IsDefinition Scheme))
  in
  let env = (Global.env ()) in (* Refresh after declare constant *)
  env, Evd.from_env env, ctx, indapp, kn

let derive_dep_elimination env sigma ~poly (i,u) =
  let env, evd, ctx, ty, gref = depcase ~poly (i,u) in
  let indid = Nametab.basename_of_global (GlobRef.IndRef i) in
  let id = add_prefix "DependentElimination_" indid in
  let evdref = ref evd in
  let cl = dependent_elimination_class evdref in
  let caseterm = e_new_global evdref gref in
  let casety = Retyping.get_type_of env !evdref caseterm in
  let args = extended_rel_vect 0 ctx in
  Equations_common.declare_instance id ~poly !evdref ctx cl
    [ty; prod_appvect sigma casety args;
     mkApp (caseterm, args)]

let () =
  let fn ~pm env sigma ~poly c =
    let _ = derive_dep_elimination env sigma ~poly c in
    pm
  in
  Ederive.(register_derive
             { derive_name = "DependentElimination"
             ; derive_fn = make_derive_ind fn })

let pattern_call ?(pattern_term=true) c =
  enter_goal (fun env sigma concl ->
  let cr = Retyping.relevance_of_term env sigma c in
  let cty = Retyping.get_type_of env sigma c in
  let ids = Id.Set.of_list (ids_of_named_context (named_context env)) in
  let deps =
    match kind sigma c with
    | App (f, args) -> Array.to_list args
    | _ -> []
  in
  let varname c = match kind sigma c with
    | Var id -> id
    | _ -> Namegen.next_ident_away (Id.of_string (Namegen.hdchar env sigma c))
        ids
  in
  let mklambda ty (c, id, cty) =
    let conclvar, _ = Find_subterm.subst_closed_term_occ env sigma
      (Locus.AtOccs Locus.AllOccurrences) c ty in
      mkNamedLambda sigma (make_annot id cr) cty conclvar
  in
  let subst =
    let deps = List.rev_map (fun c -> (c, varname c, Retyping.get_type_of env sigma c)) deps in
      if pattern_term then (c, varname c, cty) :: deps
      else deps
  in
  let concllda = List.fold_left mklambda concl subst in
  let conclapp = applistc concllda (List.rev_map pi1 subst) in
    (convert_concl ~cast:false ~check:false conclapp DEFAULTcast))

let destPolyRef sigma c =
  let open GlobRef in
  match kind sigma c with
  | Ind (ind, u) -> IndRef ind, u
  | Const (c, u) -> ConstRef c, u
  | Construct (cstr, u) -> ConstructRef cstr, u
  | _ -> raise (Invalid_argument "destPolyRef")

(** Compare up-to variables in v, skipping parameters of inductive constructors. 
    [t] is closed  
  *)

let rec compare_upto_variables sigma t v =
  if (isVar sigma v || isRel sigma v) then true
  else
    match kind sigma t, kind sigma v with
    | App (cnstr, args), App (cnstr', args') when eq_constr_nounivs sigma cnstr cnstr' &&
                                                  isConstruct sigma cnstr ->
       let cnstr, _u = destConstruct sigma cnstr in
       let real = constructor_nrealargs (Global.env()) cnstr in
       if real <= Array.length args && real <= Array.length args' then
         let args = CArray.sub args (Array.length args - real) real in
         let args' = CArray.sub args' (Array.length args' - real) real in
         CArray.for_all2 (compare_upto_variables sigma) args args'
       else
         compare_constr sigma (compare_upto_variables sigma) t v
    | _, _ -> compare_constr sigma (compare_upto_variables sigma) t v

let whd_head env sigma t =
  match kind sigma t with
  | App (eq, args) -> 
    mkApp (eq, Array.map (Tacred.whd_simpl env sigma) args)
  | _ -> t

let specialize_eqs ?with_block id =
  enter_goal begin fun env sigma concl ->
  let open Tacticals in
  let ty = lookup_named id (named_context env) |> Context.Named.Declaration.get_type in
  let evars = ref sigma in
  let unif env ctx evars c1 c2 =
    match Evarconv.unify env !evars Conversion.CONV (it_mkLambda_or_subst env c1 ctx) (it_mkLambda_or_subst env c2 ctx) with
    | exception Evarconv.UnableToUnify _ -> false
    | evm -> evars := evm; true
  in
  let rec aux block_count in_block in_eqs ctx subst acc ty =
    match kind !evars ty with
    | LetIn (na, b, t, ty) ->
      if is_global env !evars (Lazy.force coq_block) b then
        if with_block = None then aux block_count in_block in_eqs ctx subst acc (subst1 mkProp ty)
        else if (in_block || in_eqs) && Int.equal block_count 0 then acc, in_eqs, ctx, subst, (subst1 mkProp ty)
        else aux (block_count - 1) true in_eqs ctx subst acc (subst1 mkProp ty)
      else if not in_block then
        aux block_count in_block in_eqs (make_def na (Some b) t :: ctx) subst (lift 1 acc) ty
      else
        aux block_count in_block in_eqs ctx (make_def na (Some b) t :: subst) acc ty
    | Prod (na, t, b) when not in_block ->
      aux block_count false in_eqs (make_def na None t :: ctx) subst (mkApp (lift 1 acc, [| mkRel 1 |])) b
    | Prod (na, t, b) ->
      let env' = push_rel_context ctx env in
      let env' = push_rel_context subst env' in
      (* Feedback.msg_debug (str"Reducing" ++ Printer.pr_econstr_env env' !evars t ++ 
        str " in env " ++ Printer.pr_rel_context_of env' !evars); *)
      let t' = whd_head env' !evars t in
      (* Feedback.msg_debug (str"Reduced" ++ Printer.pr_econstr_env env' !evars t ++ 
        str " to " ++ Printer.pr_econstr_env env' !evars t'); *)
      (match kind !evars t' with
       | App (eq, [| eqty; x; y |]) when
           (is_global env !evars (Lazy.force logic_eq_type) eq &&
            (noccur_between !evars 1 (List.length subst) x ||
             noccur_between !evars 1 (List.length subst) y)) ->
         let _, u = destPolyRef !evars eq in
         let c, o = if noccur_between !evars 1 (List.length subst) x then x, y
           else y, x in
         let eqr = constr_of_global_univ !evars (Lazy.force logic_eq_refl, u) in
         let p = mkApp (eqr, [| eqty; c |]) in
         if ((Option.equal Int.equal with_block (Some 2) && Int.equal block_count 0) || 
              compare_upto_variables !evars c o) &&
            unif (push_rel_context ctx env) subst evars o c then
           aux block_count in_block true ctx subst (mkApp (acc, [| p |])) (subst1 p b)
         else acc, in_eqs, ctx, subst, ty
       | _ ->
         if in_eqs then
           (* aux in_block false ctx (make_def na None t :: subst) (mkApp (lift 1 acc, [| mkRel 1 |])) b *)
           acc, in_eqs, ctx, subst, ty
         else
           let e = evd_comb1 (Evarutil.new_evar ~typeclass_candidate:false env') evars t in
           aux block_count in_block false ctx (make_def na (Some e) t :: subst) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, subst, ty
  in
  let acc, worked, ctx, subst, ty = aux (match with_block with None -> 0 | Some n -> n) 
    (match with_block with None -> true | Some _ -> false) false [] [] (mkVar id) ty in
  let subst' = nf_rel_context_evar !evars subst in
  let subst'' = List.map (fun decl ->
    let (n,b,t) = to_tuple decl in
    match b with
    | Some k when isEvar !evars k -> make_assum n t
    | b -> decl) subst'
  in
  let ty = it_mkProd_or_LetIn ty subst'' in
  let acc = it_mkLambda_or_LetIn acc subst'' in
  let ty = it_mkProd_or_LetIn ty ctx in
  let acc = it_mkLambda_or_LetIn acc ctx in
  let ty = Evarutil.nf_evar !evars ty in
  let acc = Evarutil.nf_evar !evars acc in
    if worked then
      assert_replacing id acc ty
    else tclFAIL (str "Nothing to do in hypothesis " ++ Id.print id ++
                    Printer.pr_econstr_env env !evars ty
                   )
  end

exception Specialize

open Proofview.Notations

let specialize_eqs ?with_block id =
  let open Tacticals in
  Proofview.Goal.enter begin fun gl ->
  Proofview.tclORELSE (clear [id] <*> Proofview.tclZERO Specialize) begin function
  | (Specialize, _) -> specialize_eqs ?with_block id
  | e -> tclFAIL (str "Specialization not allowed on dependent hypotheses")
  end
  end

(** Printing of the patterns inferred by [dependent elimination id], in the syntax
    of [dependent elimination id as [p1 | ... | pn]]. This is used as a quick-fix
    replacement text, so it is printed on a single line. *)

let pr_elim_pattern env sigma pat =
  let rec aux ~arg pat =
    match DAst.get pat with
    | Syntax.PUVar (_, Syntax.Generated) -> str "_"
    | Syntax.PUVar (id, _) -> Id.print id
    | Syntax.PUEmpty -> str "!"
    | Syntax.PUInac c -> str "?(" ++ Printer.pr_glob_constr_env env sigma c ++ str ")"
    | Syntax.PUCstr (c, _, []) -> Printer.pr_global (GlobRef.ConstructRef c)
    | Syntax.PUCstr (c, nparams, args) ->
      (* All the arguments are given, so use [@] if some of them are implicit *)
      let impls = Impargs.select_stronger_impargs (Impargs.implicits_of_global (GlobRef.ConstructRef c)) in
      let explicit = List.exists Impargs.is_status_implicit (List.skipn_at_best nparams impls) in
      let pp = (if explicit then str "@" else mt ()) ++ Printer.pr_global (GlobRef.ConstructRef c) ++
        str " " ++ prlist_with_sep (fun () -> str " ") (aux ~arg:true) args in
      if arg then str "(" ++ pp ++ str ")" else pp
  in aux ~arg:false pat

let pr_dependent_elimination_as env sigma (id, pats) =
  h (str "dependent elimination " ++ Id.print id ++ str " as [" ++
    prlist_with_sep (fun () -> str " | ") (pr_elim_pattern env sigma) pats ++ str "]")

let warn_dependent_elimination_patterns =
  CWarnings.create ~name:"dependent-elimination-patterns" ~category:equations_category
    ~default:CWarnings.Disabled
    ~quickfix:(fun ~loc pp -> [Quickfix.make ~loc pp])
    (fun pp -> str "Patterns inferred by dependent elimination:" ++ spc () ++ pp ++ str ".")

(** In a branch [map] of the splitting of the [rel]-th variable, a variable of the
    constructor pattern can be forced to be equal to another variable of the context,
    e.g. [n0] in [vcons a n0 v] when splitting [v : vec A (S n)]. Give it the name of
    that variable rather than a fresh one. *)
let rename_forced_variables sigma rel (map : Context_map.context_map) =
  let open Context.Rel.Declaration in
  let vars = Context_map.pat_vars (List.nth map.Context_map.map_inst (pred rel)) in
  let used = Id.Set.of_list (List.map_filter (fun decl ->
    match get_name decl with Name id -> Some id | Anonymous -> None) map.Context_map.src_ctx) in
  let renaming, _ = List.fold_left2 (fun (renaming, used as acc) pat decl ->
    match pat, get_name decl with
    | Context_map.PInac c, Name id when isRel sigma c ->
      let i = destRel sigma c in
      if Int.Set.mem i vars && not (Int.Map.mem i renaming) && not (Id.Set.mem id used) then
        (Int.Map.add i id renaming, Id.Set.add id used)
      else acc
    | _ -> acc) (Int.Map.empty, used) map.Context_map.map_inst map.Context_map.tgt_ctx
  in
  let src_ctx = List.mapi (fun i decl ->
    match Int.Map.find_opt (succ i) renaming with
    | Some id -> set_name (Name id) decl
    | None -> decl) map.Context_map.src_ctx
  in { map with Context_map.src_ctx }

(* Dependent elimination using Equations. *)
let dependent_elim_tac ?loc ?patterns id : unit Proofview.tactic =
  enter_goal begin fun env sigma concl ->
    let sort = Retyping.get_sort_of env sigma concl in
    let hyps = named_context env in
    let default_loc, id = id in
    (* Keep aside the section variables. *)
    let sec_hyps, loc_hyps = CList.partition
      (fun decl ->
        let id = Context.Named.Declaration.get_id decl in
        Termops.is_section_variable_env env id) hyps in
    let env = Environ.reset_context env in
    let env = push_named_context (List.map (fun x -> Environ.SecVar, x) sec_hyps) env in

    (* Check that [id] exists in the current context. *)
    begin try
      let rec lookup k = function
        | decl :: _ when Id.equal id (Context.Named.Declaration.get_id decl) -> k
        | _ :: sign -> lookup (succ k) sign
        | [] -> raise Not_found
      in Proofview.tclUNIT (lookup 1 loc_hyps)
    with Not_found ->
      Tacticals.tclZEROMSG (str "No such hypothesis: " ++ Id.print id)
    end >>= fun rel ->

    (* We want to work in a [rel_context], not a [named_context]. *)
    let ctx, subst = Equations_common.rel_of_named_context sigma loc_hyps in
    let _, rev_subst, _ =
      let err () = assert false in
      Equations_common.named_of_rel_context ~keeplets:true err ctx in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars sigma subst concl in
    let rhs =
      let prog = Constrexpr.CHole None in
        Syntax.Program (Syntax.ConstrExpr (CAst.make prog), ([], []))
    in
    begin match patterns with
    | None ->
        (* Produce default clauses from the variable to split. *)
        let evd = ref sigma in
        begin match Covering.split_var (env, evd) rel ctx with
        | None | Some (Covering.CannotSplit _) ->
            Tacticals.tclZEROMSG (str "Could not eliminate variable " ++ Id.print id)
        | Some (Covering.Splitted (_, newctx, brs)) ->
            let brs = List.map (rename_forced_variables sigma rel) (Option.List.flatten (Array.to_list brs)) in
            let clauses_lhs = List.map Context_map.context_map_to_lhs brs in
            let clauses = List.map (fun lhs -> Syntax.Pre_clause (default_loc, lhs, Some rhs)) clauses_lhs in
            (* The pattern for [id] in each clause, to suggest an explicit [as] clause. *)
            let suggestion =
              let n = List.length ctx in
              if List.for_all (fun lhs -> Int.equal (List.length lhs) n) clauses_lhs then
                Some (List.map (fun lhs -> List.nth lhs (n - rel)) clauses_lhs)
              else None
            in
              Proofview.tclUNIT (clauses, suggestion)
        end
    | Some patterns ->
        (* For each pattern, produce a clause. *)
        let make_clause : (Syntax.user_pat_loc) -> Syntax.pre_clause =
          DAst.with_loc_val (fun ?loc pat ->
            let lhs =
              List.rev_map (fun decl ->
                let decl_id = Context.Named.Declaration.get_id decl in
                if Names.Id.equal decl_id id then DAst.make ?loc pat
                else DAst.make Syntax.(PUVar (decl_id, Generated))) loc_hyps
            in
            Syntax.Pre_clause (loc, lhs, Some rhs))
        in Proofview.tclUNIT (List.map make_clause patterns, None)
    end >>= fun (clauses, suggestion) ->
    if !debug then
    Feedback.msg_info (str "Generated clauses: " ++ fnl() ++ Syntax.pr_preclauses env sigma clauses);

    (* Produce dummy data for covering. *)
    (* FIXME Not very clean. *)
    let data =
      Covering.{
        rec_type = [None];
        flags = { poly = PolyFlags.of_univ_poly true; obligations = false; open_proof = false; with_eqns = false; with_ind = false;
          allow_aliases = false;
          tactic = !Declare.Obls.default_tactic};
        program_mode = false;
        fixdecls = [];
        intenv = Constrintern.empty_internalization_env;
        notations = []
      } in
    let program_orig_type = it_mkProd_or_LetIn ty ctx in
    let p = Syntax.{program_loc = default_loc;
                    program_id = Names.Id.of_string "dummy";
                    program_orig_type; program_sort = (ESorts.kind sigma sort);
                    program_impls = [];
                    program_implicits = [];
                    program_rec = None;
                    program_sign = ctx;
                    program_arity = ty} in

    (* Initial problem. *)
    let prob = Context_map.id_subst ctx in
    let args = Context.Rel.instance_list mkRel 0 ctx in

    let warn_suggestion = match loc, suggestion with
      | Some loc, Some pats ->
        Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
          warn_dependent_elimination_patterns ~loc (pr_dependent_elimination_as env sigma (id, pats))))
      | _ -> Proofview.tclUNIT ()
    in
    Proofview.tclTHEN (Refine.refine ~typecheck:true begin fun evars ->
      let evd = ref evars in
      (* Produce a splitting tree. *)
      let split : Splitting.splitting =
        Covering.covering env evd p data clauses [] prob [] ty
      in

      let c, ty =
        Splitting.term_of_tree env evd sort split
      in
      let c = beta_applist !evd (c, args) in
      let c = Vars.substl (List.rev rev_subst) c in
      if !Equations_common.debug then
        Feedback.msg_debug (str "refining with" ++ Printer.pr_econstr_env env !evd c);
        (!evd, c)
    end) warn_suggestion
  end

let dependent_elim_tac_expr ?patterns id : unit Proofview.tactic =
  enter_goal begin fun env sigma _ ->
    (* Interpret each pattern to then produce clauses. *)
    let patterns =
      match patterns with
      | None -> None
      | Some p ->
        let avoid = Syntax.ids_of_pats env sigma None p in
        Some (List.map (fun x -> List.hd (snd (Syntax.interp_pat env sigma [] ~avoid None x))) p)
    in dependent_elim_tac ?patterns id
  end
