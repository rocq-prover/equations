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
open Environ
open Libnames
open Vars
open Tactics
open Tacticals
open Evarutil
open Equations_common

open Syntax
open Covering
open Splitting
open Principles
open EConstr

open Extraction_plugin
                
let inline_helpers i = 
  let l = List.map (fun (cst, _) -> Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstRef cst)) i.helpers_info in
  Table.extraction_inline true l

let define_unfolding_eq ~pm env evd (flags : flags)  p unfp prog prog' ei hook =
  let info' = prog'.program_split_info in
  let info =
    { info' with base_id = prog.program_split_info.base_id;
                 helpers_info = prog.program_split_info.helpers_info @ info'.helpers_info;
                 user_obls = Id.Set.union prog.program_split_info.user_obls info'.user_obls } in
  let () = inline_helpers info in
  let funf_cst = match info'.term_id with GlobRef.ConstRef c -> c | _ -> assert false in
  let () = if PolyFlags.univ_poly flags.poly then evd := Evd.from_ustate info'.term_ustate in
  let funfc = e_new_global evd info'.term_id in
  let unfold_eq_id = add_suffix (program_id unfp) "_eq" in
  let hook_eqs _ pm =
    Global.set_strategy (Conv_oracle.EvalConstRef funf_cst) Conv_oracle.transparent;
    let () = (* Declare the subproofs of unfolding for where as rewrite rules *)
      let decl _ (_, id, _) =
        let gr =
          try Nametab.locate_constant (qualid_of_ident id)
          with Not_found -> anomaly Pp.(str "Could not find where clause unfolding lemma "
                                        ++ Names.Id.print id)
        in
        let gr = GlobRef.ConstRef gr in
        Principles.add_rew_rule ~l2r:true ~base:(info.base_id ^ "_where") gr;
        Principles.add_rew_rule ~l2r:false ~base:(info.base_id ^ "_where_rev") gr
      in
      PathMap.iter decl ei.Principles_proofs.equations_where_map
    in
    let env = Global.env () in
    let () = if not (PolyFlags.univ_poly flags.poly) then evd := (Evd.from_env env) in
    let prog' = { program_cst = funf_cst;
                  program_split_info = info }
    in
    let unfp =
      { unfp with program_info =
                    { unfp.program_info with program_id = program_id p } }
    in
    let eqninfo =
      Principles_proofs.{ equations_id = program_id p;
                          equations_where_map = ei.equations_where_map;
                          equations_f = funfc;
                          equations_prob = ei.equations_prob }
    in hook ~pm (p, Some unfp, prog', eqninfo) unfold_eq_id
  in
  let () = if not (PolyFlags.univ_poly flags.poly) then (evd := Evd.from_env (Global.env ())) in
  let sign = program_sign unfp in
  let arity = program_arity unfp in
  let stmt = it_mkProd_or_LetIn
      (mkEq (Global.env ()) evd arity (mkApp (p.program_term, extended_rel_vect 0 sign))
         (mkApp (funfc, extended_rel_vect 0 sign))) sign
  in
  let evd, stmt = Typing.solve_evars (Global.env ()) !evd stmt in
  let subproofs = Principles_proofs.extract_subprograms env evd ei.Principles_proofs.equations_where_map p unfp in
  let fold pm (name, subst, uctx, typ) =
    let typ = EConstr.Unsafe.to_constr typ in
    let typ = collapse_term_qualities uctx typ in
    let tac = Principles_proofs.prove_unfolding_sublemma info ei.Principles_proofs.equations_where_map prog.program_cst funf_cst subst in
    let cinfo = Declare.CInfo.make ~name ~typ () in
    let info = Declare.Info.make ~poly:info.poly
        ~scope:info.scope
        ~kind:(Decls.IsDefinition info.decl_kind)
        ()
    in
    let pm = Declare.Obls.add_definition ~pm ~cinfo ~info ~tactic:tac ~uctx ~opaque:false [||] in
    pm
  in
  let pm = List.fold_left fold pm subproofs in
  let tac =
    Principles_proofs.(prove_unfolding_lemma info ei.equations_where_map prog.program_cst funf_cst
      p unfp)
  in
  let stmt = collapse_term_qualities (Evd.ustate evd) (EConstr.to_constr evd stmt) in
  let cinfo = Declare.CInfo.make ~name:unfold_eq_id ~typ:stmt ~impargs:(program_impls p) () in
  let info = Declare.Info.make ~poly:info.poly
      ~scope:info.scope
      ~kind:(Decls.IsDefinition info.decl_kind)
      ()
  in
  let obl_hook = Declare.Hook.make_g hook_eqs in
  let pm =
    Declare.Obls.add_definition ~pm ~cinfo ~info ~reduce:(fun x -> x)
      ~tactic:tac ~obl_hook ~opaque:false
      ~uctx:(Evd.ustate evd) [||]
  in pm

let define_principles ~pm (flags : flags) rec_type progs =
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let () =
    if PolyFlags.univ_poly flags.poly then
      let ustate = (snd (List.hd progs)).program_split_info.term_ustate in
      let () = evd := Evd.merge_ustate !evd ustate in ()
    else ()
  in
  let pm, progs' = Principles.unfold_programs ~pm env evd flags rec_type progs in
  match progs' with
  | [p, Some (unfp, cpi'), cpi, eqi] ->
    let hook ~pm (p, unfp, cpi', eqi) unfold_eq_id =
      let cpi' = { cpi' with
                   program_split_info =
                     { cpi'.program_split_info with
                       comp_obls = cpi'.program_split_info.comp_obls @ cpi.program_split_info.comp_obls } } in
      Principles.build_equations ~pm flags.with_ind env !evd
        ~alias:(make_alias (p.program_term, unfold_eq_id, p.program_splitting))
        rec_type [p, unfp, cpi', eqi]
    in
    define_unfolding_eq ~pm env evd flags p unfp cpi cpi' eqi hook
  | splits ->
    let splits = List.map (fun (p, unfp, cpi, eqi) ->
     let unfp' = match unfp with
       | Some (unfp, unfpi) -> Some unfp
       | None -> None
     in (p, unfp', cpi, eqi)) splits
    in
    build_equations ~pm flags.with_ind env !evd rec_type splits

let define_by_eqs ~pm ~poly ~program_mode ~obligations ~tactic ~open_proof opts eqs nt =
  let with_eqns, with_ind =
    let try_bool_opt opt default =
      try List.assoc opt opts
      with Not_found -> default
    in
    let with_eqns = try_bool_opt OEquations !Equations_common.equations_derive_equations in
    if with_eqns then
      with_eqns, try_bool_opt OInd !Equations_common.equations_derive_eliminator
    else false, false
  in
  let obligations =
    match obligations with
    | Some b -> b
    | None -> Equations_common.equations_obligations () || program_mode
  in
  let env = Global.env () in
  let flags = { poly; obligations; open_proof; with_eqns; with_ind; allow_aliases = false;
    tactic } in
  let evm, udecl =
    match eqs with
    | (((loc, i), udecl, _, _, _, _), _) :: _ ->
      Constrintern.interp_univ_decl_opt env udecl
    | _ -> assert false
  in
  let evd = ref evm in
  let programs = List.map (fun (((loc,i),udecl,rec_annot,l,t,by),clauses as ieqs) ->
      let is_rec = is_recursive i (eqs, nt) in
      interp_arity env evd ~poly ~is_rec ~with_evars:open_proof nt ieqs) eqs in
  let rec_type = compute_rec_type [] programs in
  let () = print_program_info env !evd programs in
  let env = Global.env () in (* To find the comp constant *)
  let data, fixdecls, fixprots = compute_fixdecls_data env evd programs in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  let intenv = { rec_type; flags; fixdecls; intenv = data; notations = nt; program_mode } in
  let programs = coverings env evd intenv programs (List.map snd eqs) in
  let env = Global.env () in (* coverings has the side effect of defining comp_proj constants for now *)
  let fix_proto_ref = Globnames.destConstRef (Lazy.force coq_fix_proto) in
  (* let _kind = (Decl_kinds.Global Decl_kinds.ImportDefaultBehavior, poly, Decl_kinds.Definition) in *)
  let baseid =
    let p = List.hd programs in Id.to_string p.program_info.program_id in
  (* Necessary for the definition of [i] *)
  let () =
    let trs = { TransparentState.full with TransparentState.tr_cst = Cpred.complement (Cpred.singleton fix_proto_ref) } in
    Hints.create_hint_db false baseid trs true
  in
  let progs = Array.make (List.length eqs) None in
  let nt = List.map Metasyntax.prepare_where_notation nt in
  let hook ~pm i p info =
    let () = inline_helpers info in
    let f_cst = match info.term_id with GlobRef.ConstRef c -> c | _ -> assert false in
    let () = evd := Evd.from_ustate info.term_ustate in
    let compiled_info = { program_cst = f_cst;
                          program_split_info = info } in
    progs.(i) <- Some (p, compiled_info);
    if CArray.for_all (fun x -> not (Option.is_empty x)) progs then
      (let progs = Array.map_to_list (fun x -> Option.get x) progs in
       let is_relevant (rel, _) = not @@ ERelevance.is_irrelevant !evd rel in
       let relevant = List.for_all is_relevant fixprots in
       let rec_info = compute_rec_type [] (List.map (fun (x, y) -> x.program_info) progs) in
       List.iter (Metasyntax.add_notation_interpretation ~local:false (Global.env ())) nt;
       if (flags.with_eqns || flags.with_ind) && relevant then
         define_principles ~pm flags rec_info progs
       else pm)
    else pm
  in
  let hook ~pm i p info = (), hook ~pm i p info in
  define_programs ~pm env evd udecl rec_type fixdecls flags programs hook

let interp_tactic = function
  | Some qid -> 
    let open Ltac_plugin in
    let kn =
      try Tacenv.locate_tactic qid 
      with Not_found -> CErrors.user_err Pp.(str"Tactic " ++ pr_qualid qid ++ str" not found")
    in
    let genarg = Tacenv.interp_ltac kn in
    let tacval = Tacinterp.Value.closure (Tacinterp.default_ist ()) genarg in
    Tacinterp.Value.apply tacval []
  | None -> !Declare.Obls.default_tactic

let equations ~pm ~poly ~program_mode ?obligations ?tactic opts eqs nt =
  List.iter (fun (((loc, i), _udecl, nested, l, t, by),eqs) -> Dumpglob.dump_definition CAst.(make ?loc i) false "def") eqs;
  let tactic = interp_tactic tactic in
  let pm, pstate =
    define_by_eqs ~pm ~poly ~program_mode ~obligations ~tactic ~open_proof:false opts eqs nt in
  match pstate with
  | None -> pm
  | Some _ ->
    CErrors.anomaly Pp.(str"Equation.equations leaving a proof open")

let equations_interactive ~pm ~poly ~program_mode ?obligations ?tactic opts eqs nt =
  List.iter (fun (((loc, i), _udecl, nested, l, t, by),eqs) -> Dumpglob.dump_definition CAst.(make ?loc i) false "def") eqs;
  let tactic = interp_tactic tactic in
  let pm, lemma = define_by_eqs ~pm ~poly ~program_mode ~obligations ~tactic ~open_proof:true opts eqs nt in
  match lemma with
  | None ->
    CErrors.anomaly Pp.(str"Equation.equations_interactive not opening a proof")
  | Some p -> pm, p

let solve_equations_goal destruct_tac tac =
  enter_goal begin fun env sigma concl ->
  let intros, move, concl =
    let rec intros goal move = 
      match Constr.kind goal with
      | Prod ({binder_name=Name id}, _, t) ->
         let id = fresh_id_in_env id env in
         let tac, move, goal = intros (subst1 (Constr.mkVar id) t) (Some id) in
         tclTHEN intro tac, move, goal
      | LetIn ({binder_name=Name id}, c, _, t) ->
         if String.equal (Id.to_string id) "target" then 
           tclIDTAC, move, goal
         else 
           let id = fresh_id_in_env id env in
           let tac, move, goal = intros (subst1 c t) (Some id) in
           tclTHEN intro tac, move, goal
      | _ -> tclIDTAC, move, goal
    in 
    intros (to_constr sigma concl) None
  in
  let move_tac = 
    match move with
    | None -> fun _ -> tclIDTAC
    | Some id' -> fun id -> move_hyp id (Logic.MoveBefore id')
  in
  let targetn, branchesn, targ, brs, b =
    match kind sigma (of_constr concl) with
    | LetIn ({binder_name=Name target}, targ, _, b) ->
        (match kind sigma b with
        | LetIn ({binder_name=Name branches}, brs, _, b) ->
           target, branches, int_of_coq_nat (to_constr sigma targ),
           int_of_coq_nat (to_constr sigma brs), b
	| _ -> error "Unnexpected goal")
    | _ -> error "Unnexpected goal"
  in
  let branches, b =
    let rec aux n c =
      if n == 0 then [], c
      else match kind sigma c with
      | LetIn ({binder_name=Name id}, br, brt, b) ->
	  let rest, b = aux (pred n) b in
	    (id, br, brt) :: rest, b
      | _ -> error "Unnexpected goal"
    in aux brs b
  in
  let ids = targetn :: branchesn :: List.map pi1 branches in
  let cleantac = intros_using_then ids clear in
  let dotac = tclDO (succ targ) intro in
  let letintac (id, br, brt) = 
    tclTHEN (letin_tac None (Name id) br (Some brt) nowhere)
            (tclTHEN (move_tac id) tac)
  in
  let subtacs =
    tclTHENS destruct_tac (List.map letintac branches)
  in tclTHENLIST [intros; cleantac ; dotac ; subtacs]
  end

let dependencies env sigma c ctx =
  let init = global_vars_set env c in
  let deps =
    fold_named_context_reverse 
    (fun variables decl ->
      let n = get_id decl in
      let dvars = global_vars_set_of_decl env sigma decl in
        if Id.Set.mem n variables then Id.Set.union dvars variables
        else variables)
      ~init:init ctx
  in
    (init, Id.Set.diff deps init)
