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
open Context
open Constr
open Reductionops
open Pp
open List
open Evarutil
open Termops
open Equations_common
open Syntax
open Context_map
open Splitting

open EConstr
open EConstr.Vars   

type int_data = {
  rec_type : rec_type;
  fixdecls : rel_context;
  flags : flags;
  program_mode : bool;
  intenv : Constrintern.internalization_env;
  notations : Vernacexpr.notation_declaration list
}

exception Conflict
exception Stuck

type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
type unification_result =
  (context_map * int * constr * pat) option

(* let isConstruct_app_or_Rel env sigma c =
  let hd, args = decompose_app sigma c in 
  isRel sigma hd || isConstruct sigma hd *)
  
(* let maybe_reduce_to_hnf env sigma c =
  if isConstruct_app_or_Rel env sigma c then c, false
  else let c' = Tacred.hnf_constr env sigma c in
    if isConstruct_app_or_Rel env sigma c' then c', true
    else c, false *)
    
let decompose_rel evd c =
  match kind evd c with
  | Rel i -> Some i
  | _ -> None

let rec unify env evd flex g x y =
  if is_conv_leq env evd x y then id_subst g
  else
    match decompose_rel evd x with
    | Some i -> 
      if not (isRel evd y) && not (noccurn evd i y) then raise Conflict (* Occur check *)
      else if Int.Set.mem i flex then
        single_subst env evd i (PInac y) g
      else raise Stuck
    | None ->
      match decompose_rel evd y with
      | Some i ->
        if (* not (isRel evd x) &&  *)not (noccurn evd i x) then raise Conflict (* Occur check *)
        else if Int.Set.mem i flex then
          single_subst env evd i (PInac x) g
        else raise Stuck
      | None ->
        let (c, l) = decompose_app_list evd x
        and (c', l') = decompose_app_list evd y in
        if isConstruct evd c && isConstruct evd c' then
          if eq_constr evd c c' then
            unify_constrs env evd flex g l l'
          else raise Conflict
        else raise Stuck

(* and unify env evd flex g x y =
  match unify_hnfs env evd flex g x y with
  | exception e -> 
      let x, modified = maybe_reduce_to_hnf env evd x in
      let y, modified' = maybe_reduce_to_hnf env evd y in
      if modified || modified' then unify_hnfs env evd flex g x y
      else raise e
  | s -> s *)

and unify_constrs env evd flex g l l' = 
  match l, l' with
  | [], [] -> id_subst g
  | hd :: tl, hd' :: tl' ->
    (try
       let hdunif = unify env evd flex g hd hd' in
       let { src_ctx = d; map_inst = s } = hdunif in
       let specrest = List.map (specialize_constr evd s) in
       let tl = specrest tl and tl' = specrest tl' in
       let tlunif = unify_constrs env evd flex d tl tl' in
       compose_subst env ~sigma:evd tlunif hdunif
     with Stuck ->
       let tlunif = unify_constrs env evd flex g tl tl' in
       let spec = specialize_constr evd (tlunif.map_inst) in
       let hd = spec hd and hd' = spec hd' in
       let hdunif = unify env evd flex (tlunif.src_ctx) hd hd' in
       compose_subst env ~sigma:evd hdunif tlunif)
  | _, _ -> raise Conflict

let flexible pats gamma =
  let rec aux (k,flex) pats decls = 
    match decls, pats with
    | Context.Rel.Declaration.LocalAssum _ :: decls, pat :: pats ->
        (match pat with
        | PInac _ -> aux (succ k, Int.Set.add k flex) pats decls
        | p -> aux (succ k, flex) pats decls)
    | _ :: decls,  pats -> aux (succ k, flex) pats decls
    | [], [] -> flex
    | _ -> assert false
  in aux (1, Int.Set.empty) pats gamma

let rec accessible = function
  | PRel i -> Int.Set.singleton i
  | PCstr (c, l) -> accessibles l
  | PInac _ | PHide _ -> Int.Set.empty

and accessibles l =
  fold_left (fun acc p -> Int.Set.union acc (accessible p)) 
    Int.Set.empty l

let hidden = function PHide _ -> true | _ -> false

type match_subst =
  ((Loc.t option * identifier * provenance) * pat) list * (Glob_term.glob_constr * pat) list *
  (user_pat_loc * constr) list * ((Loc.t option * pat) list)

let rec match_pattern env sigma p c =
  match DAst.get p, c with
  | PUVar (i,gen), (PCstr _ | PRel _ | PHide _) -> [DAst.with_loc_val (fun ?loc _ -> (loc, i, gen)) p, c], [], [], []
  | PUCstr (c, i, pl), PCstr ((c',u), pl') -> 
    if Environ.QConstruct.equal env c c' then
      let params, args = List.chop i pl' in
      match_patterns env sigma pl args
    else raise Conflict
  | PUInac t, t' ->
    [], [t, t'], [], []
  | PUVar (i, gen), PInac t when isRel sigma t ->
    [DAst.with_loc_val (fun ?loc _ -> (loc, i, gen)) p, c], [], [], []
  | _, PInac t -> [], [], [p, t], []
  | PUEmpty, _ -> [], [], [], [DAst.with_loc_val (fun ?loc _ -> (loc, c)) p]
  | _, _ -> raise Stuck

and match_patterns env sigma pl l =
  match pl, l with
  | [], [] -> [], [], [], []
  | hd :: tl, hd' :: tl' -> 
    let l = 
      try Some (match_pattern env sigma hd hd')
      with Stuck -> None
    in
    let l' = 
      try Some (match_patterns env sigma tl tl')
      with Stuck -> None
    in
    (match l, l' with
     | Some (l, li, ri, ei), Some (l', li', ri', ei') ->
       l @ l', li @ li', ri @ ri', ei @ ei'
     | _, _ -> raise Stuck)
  | _ -> raise Conflict

open Constrintern

let matches env sigma (p : user_pats) subst = 
  try
    let p' = filter (fun x -> not (hidden x)) (rev subst.map_inst) in
    UnifSuccess (match_patterns env sigma p p')
  with Conflict -> UnifFailure | Stuck -> UnifStuck

let rec match_user_pattern env p c =
  match p, DAst.get c with
  | PRel i, t -> [i, t], []
  | PCstr ((c',_), pl'), PUCstr (c, i, pl) -> 
    if Environ.QConstruct.equal env c c' then
      let params, args = List.chop i pl' in
      match_user_patterns env args pl
    else raise Conflict
  | PCstr _, PUVar (n,gen) -> [], [n, p]
  | PInac _, _ -> [], []
  | _, _ -> raise Stuck

and match_user_patterns env pl l =
  match pl, l with
  | [], [] -> [], []
  | hd :: tl, hd' :: tl' -> 
    let l = 
      try Some (match_user_pattern env hd hd')
      with Stuck -> None
    in
    let l' = 
      try Some (match_user_patterns env tl tl')
      with Stuck -> None
    in
    (match l, l' with
     | Some (l1, l2), Some (l1', l2') -> l1 @ l1', l2 @ l2'
     | _, _ -> raise Stuck)
  | _ -> raise Conflict

let matches_user env subst (p : user_pats) = 
  try UnifSuccess (match_user_patterns env (filter (fun x -> not (hidden x)) (rev subst.map_inst)) p)
  with Conflict -> UnifFailure | Stuck -> UnifStuck

let refine_arg idx ctx =
  let before, after = List.chop idx ctx in
  let lenafter = List.length after in
  let lets_in_ctx = List.count (fun x -> Context.Rel.Declaration.is_local_def x) after in
  lenafter, lenafter - lets_in_ctx

let adjust_sign_arity env evars p clauses =
  let max_args =
    match clauses with
    | [] -> Context.Rel.nhyps p.program_sign
    | _ ->
      List.fold_left (fun acc (Pre_clause (_, lhs, rhs)) ->
          let len = List.length lhs in
          max acc len) 0 clauses
  in
  let fullty = it_mkProd_or_subst env evars p.program_arity p.program_sign in
  let evars, sign, ty =
    let rec aux evars args sign ty =
      match args with
      | 0 -> evars, sign, ty
      | n ->
        match EConstr.kind evars (whd_all (push_rel_context sign env) evars ty) with
        | Prod (na, t, b) -> aux evars (n - 1) (Context.Rel.Declaration.LocalAssum (na, t) :: sign) b
        | Evar e -> let evars', t = Evardefine.define_evar_as_product env evars e in
          aux evars' args sign t
        | _ ->
          user_err_loc (None, str "Too many patterns in clauses for this type")
    in aux evars max_args [] fullty
  in
  let check_clause (Pre_clause (loc, lhs, rhs)) =
    if List.length lhs < max_args then user_err_loc (loc, str "This clause has not enough arguments")
    else ()
  in List.iter check_clause clauses;
  let sign = do_renamings env evars sign in
  let p = { p with program_sign = sign; program_arity = ty } in
  evars, p

let lets_of_ctx env ctx evars s =
  let envctx = push_rel_context ctx env in
  let ctxs, pats, varsubst, len, ids = 
    fold_left (fun (ctx', cs, varsubst, k, ids) (id, pat) -> 
        let c = pat_constr pat in
        match pat with
        | PRel i -> (ctx', cs, (i, id) :: varsubst, k, Id.Set.add id ids)
        | _ -> 
          let ty = e_type_of envctx evars c in
          (make_def (nameR id) (Some (lift k c)) (lift k ty) :: ctx', (c :: cs),
           varsubst, succ k, Id.Set.add id ids))
      ([],[],[],0,Id.Set.empty) s
  in
  let _, _, ctx' = List.fold_right (fun decl (ids, i, ctx') ->
      let (n, b, t) = to_tuple decl in
      try ids, pred i, (make_def (nameR (List.assoc i varsubst)) b t :: ctx')
      with Not_found -> 
        let id' = Namegen.next_name_away n.Context.binder_name ids in
        Id.Set.add id' ids, pred i, (make_def (nameR id') b t :: ctx')) ctx (ids, List.length ctx, [])
  in pats, ctxs, ctx'

let env_of_rhs evars ctx env s lets = 
  let envctx = push_rel_context ctx env in
  let patslets, letslen = 
    fold_right (fun decl (acc, len) -> 
        let (_, b, _) = to_tuple decl in
        (lift (-len) (Option.get b) :: acc, succ len)) lets ([], 0) 
  in
  let pats, ctx, len = 
    let (pats, x, y) = lets_of_ctx env (lets @ ctx) evars 
        (List.map (fun (id, pat) -> id, lift_pat letslen pat) s) 
    in
    pats, x @ y, List.length x 
  in
  let pats = List.map (lift (-letslen)) pats @ patslets in
  ctx, envctx, len + letslen, pats

(* let _rename_prob_subst env ctx s =
 *   let _avoid = List.fold_left (fun avoid decl ->
 *       match get_name decl with
 *       | Anonymous -> avoid
 *       | Name id -> Id.Set.add id avoid) Id.Set.empty ctx
 *   in
 *   let varsubst, rest =
 *     fold_left (fun (varsubst, rest) ((id, gen), pat) ->
 *         match pat with
 *         | PRel i when gen = false -> ((i, id) :: varsubst, rest)
 *         | _ -> (varsubst, (id, pat) :: rest))
 *       ([], []) s
 *   in
 *   let ctx' =
 *     List.fold_left_i (fun i acc decl ->
 *         try let id = List.assoc i varsubst in
 *           Context.Rel.Declaration.set_name (Name id) decl :: acc
 *         with Not_found -> decl :: acc)
 *       1 [] ctx
 *   in
 *   (List.rev ctx', id_pats ctx, ctx) *)

let is_wf_ref id rec_type =
  let aux = function 
    | Some (Logical (nargs, (_, id'))) -> 
      if Id.equal id id' then Some nargs else None 
    | _ -> None
  in CList.find_map_exn aux rec_type

let add_wfrec_implicits rec_type c =
  let open Glob_term in
  if has_logical rec_type then
    let rec aux c =
      let maprec a = Glob_ops.map_glob_constr_left_to_right aux a in
      let mapargs ts = List.map aux ts in
      DAst.with_loc_val (fun ?loc g ->
          match g with
          | GApp (fn, args) ->
            DAst.with_loc_val (fun ?loc gfn ->
                match gfn with
                | GVar fid -> 
                  (match is_wf_ref fid rec_type with
                  | exception Not_found -> maprec c
                  | nargs -> 
                    let kind = Evar_kinds.{ qm_obligation = Define false;
                                            qm_name = Anonymous;
                                            qm_record_field = None }
                    in
                    let newarg = GHole (GQuestionMark kind) in
                    let newarg = DAst.make ?loc newarg in
                    let before, after = List.chop nargs (mapargs args) in
                    let args' = List.append before (newarg :: after) in
                    DAst.make ?loc (GApp (fn, args')))
                | _ -> maprec c) fn
          | _ -> maprec c) c
    in aux c
  else c

let interp_constr_evars_impls env sigma data expected_type c =
  let c = add_wfrec_implicits data.rec_type c in
  let imps = Implicit_quantifiers.implicits_of_glob_constr ~with_products:(expected_type == Pretyping.IsType) c in
  let flags = Pretyping.{ all_no_fail_flags with program_mode = data.program_mode } in
  let sigma, c = Pretyping.understand_tcc ~flags env sigma ~expected_type c in
  sigma, (c, imps)

let interp_glob_constr_evars_impls env sigma ctx data expected_type c =
  let sigma, (c, _) = interp_constr_evars_impls env sigma data expected_type c in
  sigma, c

let expected_type = function
  | Some ty -> Pretyping.OfType ty
  | None -> Pretyping.WithoutTypeConstraint

let interp_program_body env sigma ctx data body ty =
  match body with
  | ConstrExpr c ->
    let env = push_rel_context ctx env in
    let expected_type = expected_type ty in
    let c = intern_gen expected_type ~impls:data.intenv env sigma c in
    interp_glob_constr_evars_impls env sigma ctx data expected_type c
  | GlobConstr c ->
    let env = push_rel_context ctx env in
    interp_glob_constr_evars_impls env sigma ctx data (expected_type ty) c
  | Constr c ->
    let env = Environ.reset_with_named_context (Environ.named_context_val env) env in
    let env = push_rel_context ctx env in
    let subst =
      List.fold_left_i (fun i subst decl ->
          match get_name decl with
          | Name na -> (na, mkRel i) :: subst
          | _ -> subst) 1 [] ctx
    in
    let c = Vars.replace_vars sigma subst c in
    let sigma =
      match ty with
      | None -> fst (Typing.type_of env sigma c)
      | Some ty -> Typing.check env sigma c ty
    in
    sigma, c

let interp_program_body env evars ctx data c ty =
  let notations = List.map Metasyntax.prepare_where_notation data.notations in
  Metasyntax.with_syntax_protection (fun () ->
    let ctx' = List.map EConstr.Unsafe.to_rel_decl ctx in
    List.iter (Metasyntax.set_notation_for_interpretation (Environ.push_rel_context ctx' env) data.intenv)
      notations;
    interp_program_body env evars ctx data c ty) ()
  (* try  with PretypeError (env, evm, e) ->
   *   user_err_loc (dummy_loc,
   *                 str "Typechecking failed: " ++  Himsg.explain_pretype_error env evm e) *)
     (* | e ->
      *   user_err_loc (dummy_loc,
      *                 str "Unexpected exception raised while typing body: " ++
      *                 (match c with ConstrExpr c -> Ppconstr.pr_constr_expr c
      *                             | Constr c -> Printer.pr_econstr_env env evars c) ++
      *                 str " in environment " ++ Printer.pr_rel_context_of (push_rel_context ctx env) evars ++
      *                 str ":" ++
      *                 str (Printexc.to_string e)) *)

let interp_constr_in_rhs_env env evars data (ctx, envctx, liftn, subst) substlift c ty =
  match ty with
  | None ->
    let sigma, c = interp_program_body env !evars ctx data c None in
    let c' = substnl subst substlift c in
    let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars env sigma in
    let c' = nf_evar sigma c' in
    evars := sigma; c', Retyping.get_type_of envctx sigma c'

  | Some ty -> 
    let ty' = lift liftn ty in
    let ty' = nf_evar !evars ty' in
    let sigma, c = interp_program_body env !evars ctx data c (Some ty') in
    evars := Typeclasses.resolve_typeclasses
        ~filter:Typeclasses.all_evars env sigma;
    let c' = nf_evar !evars (substnl subst substlift c) in
    c', nf_evar !evars (substnl subst substlift ty')

let interp_constr_in_rhs env ctx evars data ty s lets c =
  try
    let env' = env_of_rhs evars ctx env s lets in
    interp_constr_in_rhs_env env evars data env' 0 c ty
  with Evarsolve.IllTypedInstance _ ->
    anomaly (str"Ill-typed instance in interp_constr_in_rhs")

let unify_type env evars before id ty after =
  try
    let next_ident_away = 
      let ctxids = ref (ids_of_rel_context before @ ids_of_rel_context after) in
      let avoid = 
        fun id -> is_global id || List.mem id !ctxids
      in 
      function id -> 
        let id' = Namegen.next_ident_away_from id avoid in 
        ctxids := id' :: !ctxids; id'
    in
    let envb = push_rel_context before env in
    let ty = nf_evar !evars ty in
    let (indf, args) = find_rectype envb !evars ty in
    let ind, params = dest_ind_family indf in
    let vs = List.map (Tacred.whd_simpl envb !evars) args in
    let params = List.map (Tacred.whd_simpl envb !evars) params in
    let cstrs = Inductiveops.type_of_constructors envb ind in
    let cstrs = 
      Array.mapi (fun i ty ->
          let ty = prod_applist !evars ty params in
          let ctx, ty = decompose_prod_decls !evars ty in
          let ctx = 
            fold_right (fun decl acc ->
                let open Context.Rel.Declaration in
                let id = match get_name decl with
                | Name id -> next_ident_away id
                | Anonymous ->
                  let x = Namegen.id_of_name_using_hdchar
                      (push_rel_context acc envb) !evars (get_type decl) Anonymous in
                  next_ident_away x
                in
                (set_name (Name id) decl :: acc))
              ctx []
          in
          let env' = push_rel_context ctx env in
          let (indf, args) = find_rectype env' !evars ty in
          let ind, params = dest_ind_family indf in
          let realargs = rels_of_ctx ~with_lets:false ctx in
          let constr = applist (mkConstructUi (ind, succ i), params @ realargs) in
          let q = inaccs_of_constrs realargs in	
          let constrpat = PCstr (((fst ind, succ i), snd ind), 
                                 inaccs_of_constrs params @ patvars_of_ctx ~with_lets:false ctx) in
          env', ctx, constr, constrpat, q, args)
        cstrs
    in
    let unify vs = 
      Array.map (fun (env', ctxc, c, cpat, q, us) -> 
          let _beforelen = length before and ctxclen = length ctxc in
          let fullctx = ctxc @ before in
          try
            let vs' = List.map (lift ctxclen) vs in
            let p1 = lift_pats ctxclen (inaccs_of_constrs (rels_of_ctx ~with_lets:false before)) in
            let flex = flexible (p1 @ q) fullctx in
            let env = push_rel_context fullctx env in
            equations_debug Pp.(fun () -> 
                str"Unifying " ++ prlist_with_sep spc (Printer.pr_econstr_env env !evars) vs' ++ spc () ++
                str"and" ++ spc () ++ prlist_with_sep spc (Printer.pr_econstr_env env !evars) us);
            let s = unify_constrs env !evars flex fullctx vs' us in
            equations_debug Pp.(fun () -> str"Unification success");
            UnifSuccess (s, ctxclen, c, cpat)
          with Conflict -> 
            equations_debug Pp.(fun () -> str"Unification raised a conflict");
            UnifFailure 
          | Stuck -> 
            equations_debug Pp.(fun () -> str"Unification got stuck");
            UnifStuck) cstrs
    in 
    let res = unify vs in
    if Array.exists (fun x -> x == UnifStuck) res then
      let vs' = List.map (Tacred.hnf_constr envb !evars) args in
      let res' = unify vs' in
      if not (Array.exists (fun x -> x == UnifStuck) res') then 
        let newty = applist (mkIndU ind, params @ vs') in
        Some (newty, res')
      else
        let newty = applist (mkIndU ind, params @ vs) in
        Some (newty, res)
    else 
      let newty = applist (mkIndU ind, params @ vs) in
      Some (newty, res)
  with Not_found -> (* not an inductive type *)
    equations_debug Pp.(fun () -> str"Unification raised Not_found");
    None

let blockers env curpats (subst : context_map) =
  let rec pattern_blockers p c =
    match DAst.get p, c with
    | PUVar (i, _), t -> []
    | PUCstr (c, i, pl), PCstr ((c',_), pl') -> 
      if Environ.QConstruct.equal env c c' then patterns_blockers pl (snd (List.chop i pl'))
      else []
    | PUInac _, _ -> []
    | _, PRel i -> [i]
    | _, _ -> []

  and patterns_blockers pl l =
    match pl, l with
    | [], [] -> []
    | hd :: tl, PHide _ :: tl' -> patterns_blockers pl tl'
    | hd :: tl, hd' :: tl' -> 
      (pattern_blockers hd hd') @ (patterns_blockers tl tl')
    | _ -> []

  in patterns_blockers curpats (rev subst.map_inst)

let subst_matches_constr sigma k s c =
  let rec aux depth c =
    match kind sigma c with
    | Rel n -> 
      let k = n - depth in 
      if k >= 0 then 
        try lift depth (assoc k s)
        with Not_found -> c
      else c
    | _ -> map_with_binders sigma succ aux depth c
  in aux k c

let is_all_variables (delta, pats, gamma) =
  List.for_all (function PInac _ | PHide _ -> true | PRel _ -> true | PCstr _ -> false) pats

type 'a split_var_result =
  | Splitted of 'a
  | CannotSplit of Names.Name.t * rel_context * constr

let split_var (env,evars) var delta =
  (* delta = before; id; after |- curpats : gamma *)	    
  let before, decl, after = split_tele (pred var) delta in
  let (id, b, ty) = to_tuple decl in
  let unify = unify_type env evars before id ty after in
  let branch = function
    | UnifFailure -> None
    | UnifStuck -> assert false
    | UnifSuccess (map, ctxlen, cstr, cstrpat) ->
      let { src_ctx = ctx'; map_inst = s; tgt_ctx = ctx } = map in
      (* ctx' |- s : before ; ctxc *)
      (* ctx' |- cpat : ty *)
      if !debug then Feedback.msg_debug Pp.(str"cpat: " ++ pr_pat env !evars cstrpat);
      let cpat = specialize !evars s cstrpat in
      let ctx' = do_renamings env !evars ctx' in
      (* ctx' |- spat : before ; id *)
      let spat =
        let ctxcsubst, beforesubst = List.chop ctxlen s in
        let map = { src_ctx = ctx'; map_inst = cpat :: beforesubst; tgt_ctx = decl :: before } in
        check_ctx_map env !evars map
      in
      (* ctx' ; after |- safter : before ; id ; after = delta *)
      Some (lift_subst env !evars spat after)
  in
  match unify with
  | None -> None
  | Some (newty, unify) ->
    (* Some constructor's type is not refined enough to match ty *)
    if Array.exists (fun x -> x == UnifStuck) unify then
      Some (CannotSplit (id.binder_name, before, newty))
    else
      let newdelta = after @ (make_def id b newty :: before) in
      Some (Splitted (var, do_renamings env !evars newdelta, Array.map branch unify))

let prove_empty env delta v =
  match split_var env v delta with
  | None -> None
  | Some (CannotSplit _) -> None
  | Some (Splitted (v, i, r)) ->
    if CArray.for_all (fun x -> x == None) r then
      Some (v, i, CArray.map (fun _ -> None) r)
    else None

let find_empty env delta =
  let r = List.map_filter (fun v -> prove_empty env delta v)
      (CList.init (List.length delta) succ)
  in match r with x :: _ -> Some x | _ -> None

(* The list of variables appearing in a list of patterns,
   ordered increasingly. *)
let variables_of_pats pats = 
  let rec aux acc pats = 
    List.fold_right (fun p acc ->
        match p with
        | PRel i -> (i, false) :: acc
        | PCstr (c, ps) -> aux [] (rev ps) @ acc
        | PInac c -> acc
        | PHide i -> (i, true) :: acc)
      pats acc
  in List.sort (fun (i, _) (i', _) -> i - i') (aux [] pats)

let pats_of_variables = List.map (fun (i, hide) ->
    if hide then PHide i else PRel i)

let lift_rel_declaration k decl = map_rel_declaration (lift k) decl

let lookup_named_i id =
  let rec aux i = function
    | decl :: _ when Id.equal id (get_id decl) -> i, decl
    | _ :: sign -> aux (succ i) sign
    | [] -> raise Not_found
  in aux 1

let instance_of_pats env evars (ctx : rel_context) (pats : (int * bool) list) =
  let subst, _, nctx = named_of_rel_context (fun () -> raise (Invalid_argument "named_of_rel_context")) ctx in
  let subst = List.map (destVar evars) subst in
  let ctx' =
    List.fold_right (fun (i, hide) ctx' ->
        let decl =
          let id = List.nth subst (pred i) in
          let i, decl = lookup_named_i id nctx in
          decl
        in decl :: ctx')
      pats []
  in
  let pats' =
    List.map_i (fun i id ->
        let i', _ = lookup_named_i id ctx' in
        CList.find_map_exn (fun (i'', hide) ->
            if i'' == i then Some (if hide then PHide i' else PRel i')
            else None) pats)
      1 subst
  in
  let pats'' =
    List.map_i (fun i decl ->
        let (id, b, t) = to_named_tuple decl in
        let i', _ = lookup_named_i id.binder_name nctx in
        CList.find_map_exn (fun (i'', hide) ->
            if i'' == i' then Some (if hide then PHide i else PRel i)
            else None) pats)
      1 ctx'
  in fst (rel_of_named_context evars ctx'), pats', pats''

let push_rel_context_eos ctx env evars =
  if named_context env <> [] then
    let env' =
      push_named ProofVar
        (make_named_def (annotR coq_end_of_section_id)
           (Some (get_efresh coq_the_end_of_the_section evars))
           (get_efresh coq_end_of_section evars)) env
    in push_rel_context ctx env'
  else push_rel_context ctx env

let split_at_eos env sigma ctx =
  List.split_when (fun decl ->
      is_lglobal env sigma coq_end_of_section (get_named_type decl)) ctx

let pr_problem p env sigma { src_ctx = delta; map_inst = patcs }=
  let env' = push_rel_context delta env in
  let ctx = pr_context env sigma delta in
  Id.print p.program_id ++ str" " ++ pr_pats env' sigma patcs ++
  (if List.is_empty delta then ctx else 
     fnl () ++ str "In context: " ++ fnl () ++ ctx)

let rel_id ctx n = 
  Nameops.Name.get_id (pi1 (List.nth ctx (pred n)))

let check_unused_clauses env sigma cl =
  let unused = List.filter (fun (_, (_, used)) -> used = 0) cl in
  match unused with
  | (Pre_clause (loc, lhs, _) as cl, _) :: cls ->
    user_err_loc (loc, str "Unused clause " ++ pr_preclause env sigma cl)
  | [] -> ()


let compute_rec_type context programs =
  if List.for_all (fun p -> match p.Syntax.program_rec with
      | None -> true
      | Some _ -> false) programs then None :: context
  else if List.for_all (fun p -> match p.Syntax.program_rec with
      | Some (Structural _)
      | None -> true
      | _ -> false) programs then
    let recids =
      List.map (fun p -> p.program_id,
                         match p.program_rec with
                         | Some (Structural ann) -> ann
                         | None -> NestedNonRec
                         | _ -> assert false) programs
    in Some (Guarded recids) :: context
  else begin
    if List.length programs != 1 then
      user_err_loc (None, Pp.str "Mutual well-founded definitions are not supported");
    let p = List.hd programs in
    match p.program_rec with
    | Some (WellFounded (_, _, id)) -> 
      let nargs = Context.Rel.nhyps p.program_sign in
      Some (Logical (nargs, id)) :: context
    | _ -> assert false
  end

let print_program_info env sigma programs =
  let open Pp in
  if !Equations_common.debug then
    Feedback.msg_debug (str "Programs: " ++ prlist_with_sep fnl (pr_program_info env sigma) programs)

let make_fix_proto env sigma ty =
  let relevance = Retyping.relevance_of_type env sigma ty in
  let _, fixproto = get_fresh sigma coq_fix_proto in
  let r = Retyping.relevance_of_term env sigma fixproto in
  let na = make_annot Anonymous r in
  relevance, mkLetIn (na, fixproto, Retyping.get_type_of env sigma fixproto, lift 1 ty)

let compute_fixdecls_data env evd ?data programs =
  let protos = List.map (fun p ->
      let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
      (p.program_id, ty, p.program_impls)) programs
  in
  let names, tys, impls = List.split3 protos in
  let data =
    Constrintern.compute_internalization_env ?impls:data
    env !evd Constrintern.Recursive names tys impls
  in
  let fixprots = List.map (fun ty -> make_fix_proto env !evd ty) tys in
  let fixdecls =
    List.map2 (fun i (relevance, fixprot) -> of_tuple (make_annot (Name i) relevance, None, fixprot)) names fixprots in
  data, List.rev fixdecls, fixprots

let interp_arity env evd ~poly ~is_rec ~with_evars notations (((loc,i),udecl,rec_annot,l,t,by),clauses as ieqs) =
  let ienv, ((env', sign), impls, _locs) = Equations_common.evd_comb1 (interp_context_evars env) evd l in
  let (arity, impls') =
    let ty = match t with
      | Some ty -> ty
      | None -> CAst.make ?loc (Constrexpr.CHole None)
    in
    Equations_common.evd_comb1 (interp_type_evars_impls env' ?impls:None) evd ty
  in
  let impls = impls @ impls' in
  let sigma = Evd.minimize_universes !evd in
  let sign = nf_rel_context_evar sigma sign in
  let arity = nf_evar sigma arity in
  let interp_reca k i =
    match k with
    | None | Some Syntax.Mutual -> MutualOn i
    | Some Nested -> NestedOn i
  in
  let rec_annot =
    match by with
    | None ->
      (if is_rec then
         if rec_annot = Some Syntax.Nested && not (is_recursive i ([ieqs], notations)) then
           (* Nested but not recursive in in its own body *)
           Some (Structural NestedNonRec)
         else Some (Structural (interp_reca rec_annot None))
       else None)
    | Some (Structural lid) ->
      (match lid with
       | Some lid ->
         (try
            let k, _, _ = lookup_rel_id (snd lid) sign in
            Some (Structural (interp_reca rec_annot (Some (List.length sign - k, Some lid))))
          with Not_found ->
            user_err_loc (fst lid,
                          Pp.(str"No argument named " ++ Id.print (snd lid) ++ str" found")))
       | None -> Some (Structural (interp_reca rec_annot None)))
    | Some (WellFounded (c, r)) -> Some (WellFounded (c, r))
  in
  let body = it_mkLambda_or_LetIn arity sign in
  let _ = if not with_evars then Pretyping.check_evars env !evd body in
  let program_orig_type = it_mkProd_or_LetIn arity sign in
  let program_sort =
    let u = Retyping.get_sort_of env !evd program_orig_type in
    let sigma, sortl, sortu = nonalgebraic_universe_level_of_universe env !evd u in
    evd := sigma; ESorts.kind sigma sortu
  in
  let program_implicits = Impargs.compute_implicits_with_manual env !evd program_orig_type false impls in
  let () = evd := Evd.minimize_universes !evd in
  match rec_annot with
  | None ->
    { program_loc = loc;
      program_id = i;
      program_orig_type;
      program_sort;
      program_sign = sign;
      program_arity = arity;
      program_rec = None;
      program_impls = impls;
      program_implicits }
  | Some (Structural ann) ->
    { program_loc = loc;
      program_id = i;
      program_orig_type;
      program_sort;
      program_sign = sign;
      program_arity = arity;
      program_rec = Some (Structural ann);
      program_impls = impls;
      program_implicits }
  | Some (WellFounded (c, r)) ->
    let compinfo = (loc, i) in
    { program_loc = loc;
      program_id = i;
      program_orig_type;
      program_sort;
      program_sign = sign;
      program_arity = arity;
      program_rec = Some (WellFounded (c, r, compinfo));
      program_impls = impls;
      program_implicits }

let recursive_patterns env progid rec_info =
  match rec_info with
  | Some (Guarded l) :: _ ->
    let addpat (id, k) =
      match k with
      | NestedNonRec when Id.equal id progid -> None
      | _ -> Some (DAst.make (PUVar (id, User)))
    in
    let structpats = List.map_filter addpat l in
    structpats
  | _ -> []

let destPRel = function PRel i -> i | _ -> assert false

let pats_of_sign sign =
  List.rev_map (fun decl ->
      DAst.make (PUVar (Name.get_id (Context.Rel.Declaration.get_name decl), Implicit))) sign

let abstract_term_in_context env evars idx t map =
  let before, after = CList.chop (pred idx) map.src_ctx in
  let before' = subst_term_in_context evars (lift (- pred idx) t) before in
  { src_ctx = before' @ after; map_inst = map.map_inst; tgt_ctx = map.tgt_ctx }

let wf_fix_constr env evars sign arity sort carrier cterm crel =
  let sigma, tele, telety = Sigma_types.telescope_of_context env !evars sign in
  let () = evars := sigma in
  let concl = it_mkLambda_or_LetIn arity sign in
  let crel = mkapp env evars logic_tele_measure [| tele; carrier; cterm; crel |] in
  let wfty = mkapp env evars logic_wellfounded_class [| telety; crel |] in
  let sigma, wf = new_evar env !evars wfty in
  let sigma = Typeclasses.resolve_typeclasses env sigma in
  let () = evars := sigma in
  let fix =
    (* let _, tyrelu = destConst sigma (fst (decompose_app sigma wfty)) in *)
    (* if not (EInstance.is_empty tyrelu) then
     *   let sigma, inst, glu = Equations_common.instance_of env !evars ~argu:tyrelu sort in
     *   let () = evars := sigma in
     *   mkApp (EConstr.mkRef (Lazy.force logic_tele_fix, inst), [| tele; crel; wf; concl|])
     * else *)
    mkapp env evars logic_tele_fix [| tele; crel; wf; concl|]
  in
  let sigma, fixty = Typing.type_of env !evars fix in
  let () = evars := sigma in
  let reds =
    let flags = RedFlags.betaiotazeta in
    let csts =
      let ts = TransparentState.empty in
      let tr_prj = Names.PRpred.add (Projection.repr (Lazy.force coq_pr1)) Names.PRpred.empty in
      let tr_prj = Names.PRpred.add (Projection.repr (Lazy.force coq_pr2)) tr_prj in
      let cst = Names.Cpred.empty in
      let add_ts cst t = Names.Cpred.add (Globnames.destConstRef (Lazy.force t)) cst in
      let tr_cst = List.fold_left add_ts cst
          [logic_tele_interp;
           logic_tele_measure;
           logic_tele_fix;
           logic_tele_MR;
           logic_tele_fix_functional_type;
           logic_tele_type_app;
           logic_tele_forall_type_app;
           logic_tele_forall_uncurry;
           logic_tele_forall;
           logic_tele_forall_pack;
           logic_tele_forall_unpack]
      in { ts with TransparentState.tr_cst; TransparentState.tr_prj }
    in RedFlags.red_add_transparent flags csts
  in
  let norm env =
    let infos = Cbv.create_cbv_infos reds ~strong:true env !evars in
    Cbv.cbv_norm infos
  in
  let fixty = norm env fixty in
  (* let prc = Printer.pr_econstr_env env !evars in
   * Feedback.msg_debug (str" fix ty" ++ prc fixty); *)
  let functional_type, concl =
    match kind !evars fixty with
    | Prod (na, fnty, concl) ->
      let concl = subst1 mkProp concl in
      fnty, concl
    | _ -> assert false
  in
  let fix = norm env fix in
  let functional_type, full_functional_type =
    let ctx, rest = Reductionops.whd_decompose_prod_n_assum env !evars (Context.Rel.nhyps sign) functional_type in
    match kind !evars (whd_all (push_rel_context ctx env) !evars rest) with
    | Prod (na, b, concl) ->
      let ctx', rest = Reductionops.whd_decompose_prod_decls (push_rel_context ctx env) !evars b in
      let infos = Cbv.create_cbv_infos reds ~strong:true (push_rel_context ctx env) !evars in
      let norm = Cbv.cbv_norm infos in
      let fn_type = it_mkProd_or_LetIn rest ctx' in
      let fn_type = norm fn_type in
      fn_type, it_mkProd_or_LetIn (mkProd (na, fn_type, concl)) ctx
    | _ -> assert false
  in
  (* let sigma, functional_evar = new_evar env !evars functional_type in *)
  (* let fix = mkApp (fix, [| functional_evar |]) in *)
  (* Feedback.msg_debug (str" rec definition" ++
   *                     str" fix: " ++ prc fix ++
   *                     str " functional type : " ++ prc functional_type ++
   *                     str " full functional type : " ++ prc full_functional_type ++
   *                     str " conclusion type : " ++ prc concl); *)
  functional_type, full_functional_type, fix

let wf_fix env evars subst sign arity sort term rel =
  let envsign = push_rel_context sign env in
  let sigma, cterm = interp_constr_evars envsign !evars term in
  let na, carrier =
    let r = Retyping.relevance_of_term envsign sigma cterm in
    let ty = Retyping.get_type_of envsign sigma cterm in
    let ty = nf_all envsign sigma ty in
    if noccur_between sigma 1 (length sign) ty then
      make_annot Anonymous r, lift (- length sign) ty
    else
      user_err_loc (Constrexpr_ops.constr_loc term,
                    str"The carrier type of the recursion order cannot depend on the arguments")
  in
  let cterm = it_mkLambda_or_LetIn cterm sign in
  (* let cterm = substl subst cterm in *)
  let sigma, rsort = Evd.fresh_sort_in_quality sigma (Lazy.force Equations_common.logic_sort) in
  let sigma, crel =
    let relty =
      (mkProd (na, carrier, mkProd (na, lift 1 carrier, mkSort rsort)))
    in
    match rel with
    | Some rel -> interp_casted_constr_evars env sigma rel relty
    | None -> new_evar env sigma relty
  in
  let () = evars := sigma in
  let res = wf_fix_constr env evars sign arity sort carrier cterm crel in
  nf_evar !evars cterm, nf_evar !evars crel, res

let compute_rec_data env evars data lets subst p =
  match p.Syntax.program_rec with
  | Some (Structural ann) ->
    let reclen, sign =
      match ann with
      | NestedNonRec -> (* Actually the definition is not self-recursive *)
        let fixdecls =
          List.filter (fun decl ->
              let na = Context.Rel.Declaration.get_name decl in
              let id = Nameops.Name.get_id na in
              not (Id.equal id p.program_id)) data.fixdecls
        in
        let len = length fixdecls in
        len, lift_rel_context len p.program_sign @ fixdecls
      | _ ->
        let len = length data.fixdecls in
        len, lift_rel_context len p.program_sign @ data.fixdecls
    in
    let extpats = recursive_patterns env p.program_id data.rec_type in
    let sign, ctxpats =
      let sign = sign @ lets in
      let extpats' = pats_of_sign lets in
      sign, extpats' @ extpats
    in
    let rec_node =
      let info =
        { struct_rec_arg = ann;
          struct_rec_protos = List.length extpats }
      in StructRec info
    in
    let rec_info =
      { rec_sign = sign;
        rec_lets = lets;
        rec_prob = id_subst sign;
        rec_arity = liftn reclen (succ (length p.program_sign)) p.program_arity;
        rec_args = List.length p.program_sign;
        rec_node }
    in
    p, rec_info.rec_prob, rec_info.rec_arity, ctxpats, (Some rec_info)

  | Some (WellFounded (term, rel, _)) ->
    let arg, rel, (functional_type, _full_functional_type, fix) =
      wf_fix env evars subst p.program_sign p.program_arity p.program_sort term rel in
    let ctxpats = pats_of_sign lets in
    let rec_args = List.length p.program_sign in
    let decl = make_def (nameR p.program_id) None functional_type in
    let rec_sign = p.program_sign @ lets in
    let lhs = decl :: rec_sign in
    let pats = PHide 1 :: lift_pats 1 (id_pats rec_sign) in
    let rec_prob = { src_ctx = lhs; map_inst = pats; tgt_ctx = lhs } in
    let rec_node =
      { wf_rec_term = fix;
        wf_rec_functional = None;
        wf_rec_arg = arg;
        wf_rec_rel = rel}
    in
    let rec_info = { rec_sign;
                     rec_lets = lets;
                     rec_arity = lift 1 p.program_arity;
                     rec_prob;
                     rec_args;
                     rec_node = WfRec rec_node }
    in
    let p = { p with program_sign = p.program_sign @ lets } in
    p, rec_info.rec_prob, rec_info.rec_arity, ctxpats, Some rec_info

  | _ ->
    let p = { p with program_sign = p.program_sign @ lets } in
    p, id_subst p.program_sign, p.program_arity, pats_of_sign lets, None

exception UnfaithfulSplit of (Loc.t option * Pp.t)

let rename_domain env sigma bindings map =
  let open Context.Rel.Declaration in
  let { src_ctx = ctx; map_inst = p; tgt_ctx = ctx' } = map in
  let avoid =
    Int.Map.fold
      (fun i (id, inacc, generated) acc -> if generated != Generated then Id.Set.add id acc else acc)
      bindings Id.Set.empty
  in
  let ctx, avoid =
    List.fold_right_map (fun decl avoid ->
      let id = Namegen.next_name_away (get_name decl) avoid in
      set_name (Name id) decl, Id.Set.add id avoid) ctx avoid in
  let fn rel decl = 
    match Int.Map.find rel bindings with
    | exception Not_found -> decl
    | (id, _, gen) -> if gen != Generated then set_name (Name id) decl else decl
  in 
  let rctx = CList.map_i fn 1 ctx in
  mk_ctx_map env sigma rctx p ctx'

let rec eq_pat_mod_inacc env sigma p1 p2 =
  match p1, p2 with
  | (PRel i | PHide i), (PRel i' | PHide i') -> Int.equal i i'
  | PCstr (c, pl), PCstr (c', pl') -> Environ.QConstruct.equal env (fst c) (fst c') && 
    List.for_all2 (eq_pat_mod_inacc env sigma) pl pl'
  | PRel i, PInac c when isRel sigma c -> Int.equal i (destRel sigma c)
  | PInac c, PRel i when isRel sigma c -> Int.equal i (destRel sigma c)
  | PInac c, PInac c' -> EConstr.eq_constr sigma c c'
  | _, _ -> false

let loc_before loc loc' =
  match loc, loc' with
  | None, Some _ -> true
  | Some _, None -> false
  | None, None -> true
  | Some loc, Some loc' ->
    let start, end_ = Loc.unloc loc in
    let start', end' = Loc.unloc loc' in
    end_ < end' || (end_ = end' && start <= start')

let rec covering_aux env evars p data prev (clauses : (pre_clause * (int * int)) list) path
    prob extpats lets ty =
  let { src_ctx = ctx; map_inst = pats; tgt_ctx = ctx' } = prob in
  if !Equations_common.debug then
    Feedback.msg_debug Pp.(str"Launching covering on "++ pr_preclauses env !evars (List.map fst clauses) ++
                           str " with problem " ++ pr_problem p env !evars prob ++
                           str " extpats " ++ pr_user_pats env !evars extpats);
  match clauses with
  | (Pre_clause (loc, lhs, rhs), (idx, cnt) as clause) :: clauses' ->
    if !Equations_common.debug then
      Feedback.msg_debug (str "Matching " ++ pr_user_pats env !evars (extpats @ lhs) ++ str " with " ++
                          pr_problem p env !evars prob);
    (match matches env !evars (extpats @ lhs) prob with
     | UnifSuccess (s, uacc, acc, empties) ->
       if !Equations_common.debug then Feedback.msg_debug (str "succeeded with substitution: " ++ 
        prlist_with_sep spc (fun ((loc, x, prov), pat) -> 
        hov 2 (pr_provenance ~with_gen:true (Id.print x) prov ++ str" = " ++ pr_pat env !evars pat ++ spc ())) s);
       let _check_aliases = 
        let check acc ((loc, x, gen), pat) =
          match Id.Map.find x acc with
          | exception Not_found -> Id.Map.add x (loc, gen, pat) acc
          | (loc', gen', pat') ->
              if eq_pat_mod_inacc env !evars pat pat' then 
                if gen == Generated then Id.Map.add x (loc', gen', pat') acc
                else Id.Map.add x (loc, gen, pat) acc
              else if data.flags.allow_aliases then acc
              else 
                let env = push_rel_context prob.src_ctx env in
                let loc, pat, pat' = 
                  if loc_before loc loc' then loc', pat, pat'
                  else loc, pat', pat
                in
                user_err_loc (loc,
                  Pp.(str "The pattern " ++ Id.print x ++ str " would shadow a variable." ++ fnl () ++
                  str "The full patterns are: " ++ pr_user_pats ~with_gen:false env !evars (extpats @ lhs) ++ fnl () ++
                  str"After interpretation, in context " ++ spc () ++ pr_context env !evars (rel_context env) ++ spc () ++
                  Id.print x ++ str " refers to " ++ pr_pat env !evars pat ++ str " while the pattern refers to " ++
                  pr_pat env !evars pat'))
          in ignore (List.fold_left check Id.Map.empty s)
       in
       let bindings, s = CList.fold_left (fun (bindings, s) ((loc, x, gen), y) ->
          let pat = 
            match y with
            | PRel i -> Some (i, false)
            | PInac i when isRel !evars i -> Some (destRel !evars i, true)
            | _ -> None 
          in
          match pat with
          | Some (i, inacc) -> begin
            match Int.Map.find i bindings with
            | exception Not_found -> (Int.Map.add i (x, inacc, gen) bindings, s)
            | (x', inacc', gen') -> begin
              match gen, gen' with
              | Generated, (User | Implicit) -> (Int.Map.add i (x', inacc && inacc', gen') bindings, s)
              | Generated, Generated -> (Int.Map.add i (x, inacc && inacc', gen) bindings, s)
              | _, Generated -> (Int.Map.add i (x, inacc && inacc', gen) bindings, s)
              | _, _ -> 
                if not (Id.equal x x') then
                  (* We allow aliasing of implicit variable names resulting from forcing a pattern *)
                  if not data.flags.allow_aliases && (gen == User && gen' == User) then
                    user_err_loc (loc,
                      Pp.(str "The pattern " ++ Id.print x ++ str " should be equal to " ++ Id.print x' ++ str", it is forced by typing"))
                  else (bindings, (x, y) :: s)
                else (bindings, s)
              end
            end
          | None -> (bindings, (x, y) :: s)) 
          (Int.Map.empty, []) s
           (* @ List.filter_map (fun (x, y) ->
            match DAst.get x with
            | PUVar (id, gen) -> Some ((DAst.with_loc_val (fun ?loc _ -> loc) x, id, gen), PInac y)
            | _ -> None) acc) *)
        in
        if !Equations_common.debug then Feedback.msg_debug (str "Renaming problem: " ++
          hov 2 (pr_context_map env !evars prob) ++ str " with bindings " ++ 
          prlist_with_sep spc (fun (i, (x, inacc, gen)) -> str "Rel " ++ int i ++ str" = " ++ 
          pr_provenance ~with_gen:true (Id.print x) gen ++ 
          str", inacc = " ++ bool inacc) (Int.Map.bindings bindings));
       let prob = rename_domain env !evars bindings prob in
       if !Equations_common.debug then Feedback.msg_debug (str "Renamed problem: " ++ 
        hov 2 (pr_context_map env !evars prob));
       (* let sext =
        List.filter_map (fun (i, (x, inacc, gen)) -> 
          if gen then None
          else Some (x, if inacc then PInac (mkRel i) else PRel i)) (Int.Map.bindings bindings) in  *)
       let s = (s, uacc, acc) in
       if !Equations_common.debug then Feedback.msg_debug (str "Substitution: " ++ 
        prlist_with_sep spc (fun (x, t) -> str "var " ++ Id.print x ++ str" = " ++ pr_pat env !evars t) 
          (pi1 s));
       (* let prob = compose_subst env ~sigma:!evars renaming prob in *)
       let clauseid = Id.of_string ("clause_" ^ string_of_int idx ^
                                    (if cnt = 0 then "" else "_" ^ string_of_int cnt)) in
       (match empties, rhs with
        | ([], None) ->
          user_err_loc (loc,
                        (str "Empty clauses should have at least one empty pattern."))
        | (_ :: _, Some _) ->
          user_err_loc (loc,
                        (str "This clause has an empty pattern, it cannot have a right hand side."))
        | (loc, c) :: _, None ->
          (match c with
          | PCstr _ | PInac _ | PHide _ ->
             user_err_loc (loc,
                           (str "This pattern cannot be empty, it matches value " ++ fnl () ++
                            pr_pat env !evars c))
          | PRel i ->
            match prove_empty (env,evars) prob.src_ctx i with
            | Some (i, ctx, s) ->
              Some (List.rev prev @ ((Pre_clause (loc, lhs, rhs),(idx, cnt+1)) :: clauses'),
                    Compute (prob, [], ty, REmpty (i, s)))
            | None ->
              user_err_loc (loc,
                            (str "This variable does not have empty type in current problem" ++ fnl () ++
                             pr_problem p env !evars prob)))
        | [], Some rhs ->
          let interp =
            interp_clause env evars p data prev clauses' (clauseid :: path) prob
              extpats lets ty ((loc,lhs,rhs), cnt) s
          in
          (match interp with
           | None ->
             user_err_loc
               (dummy_loc,
                str"Clause " ++ pr_preclause env !evars (Pre_clause (loc, lhs, Some rhs)) ++
                str" matched but its interpretation failed")
           | Some s -> Some (List.rev prev @ (Pre_clause (loc,lhs,Some rhs),(idx, cnt+1)) :: clauses', s)))

     | UnifFailure ->
       if !Equations_common.debug then Feedback.msg_debug (str "failed");
       covering_aux env evars p data (clause :: prev) clauses' path prob extpats lets ty

     | UnifStuck -> 
       if !Equations_common.debug then Feedback.msg_debug (str "got stuck");
       let blocks = blockers env (extpats @ lhs) prob in
       equations_debug (fun () ->
           str "blockers are: " ++
           prlist_with_sep spc (pr_rel_name (push_rel_context prob.src_ctx env)) blocks);
       let rec try_split acc vars =
         match vars with
         | [] -> None
         | var :: vars ->
           equations_debug (fun () -> str "trying next blocker " ++
                                      pr_rel_name (push_rel_context prob.src_ctx env) var);
           match split_var (env,evars) var prob.src_ctx with
           | Some (Splitted (var, newctx, s)) ->
             equations_debug (fun () ->
                 str "splitting succeded for " ++
                 pr_rel_name (push_rel_context prob.src_ctx env) var);
             let prob' = { src_ctx = newctx; map_inst = pats; tgt_ctx = ctx' } in
             let coverrec clauses s =
               covering_aux env evars p data []
                 clauses path
                 (compose_subst env ~sigma:!evars s prob')
                 extpats
                 (specialize_rel_context !evars s.map_inst lets)
                 (specialize_constr !evars s.map_inst ty)
             in
             (try
                let rec_call clauses x =
                  match x with (* Succesful split on this blocker *)
                  | Some s ->
                    (match coverrec clauses s with
                     | None -> raise Not_found
                     | Some (clauses, s) ->
                       equations_debug (fun _ -> str "covering succeeded");
                       clauses, Some s)
                  | None -> clauses, None
                in
                let clauses, rest = Array.fold_left_map rec_call (List.rev prev @ clauses) s in
                Some (Splitted (clauses, Split (prob', var, ty, rest)))
              with
              | Not_found ->
                equations_debug
                  (fun _ -> str "covering failed to produce a splitting in one of the branches,\
                                 trying the next one");
                try_split acc vars
              | UnfaithfulSplit (loc, pp) ->
                equations_debug
                  (fun _ -> str "covering is not faithful to user clauses, trying the next one");
                try_split acc vars)
           | Some (CannotSplit _) as x ->
             equations_debug (fun () ->
                 str "splitting failed for " ++
                 pr_rel_name (push_rel_context prob.src_ctx env) var);
             let acc = match acc with
               | None -> x
               | _ -> acc
             in try_split acc vars
           | None -> (* Not inductive *) try_split acc vars
       in
       let result = try_split None blocks in
       (match result with
        | Some (Splitted (clauses, s)) -> Some (clauses, s)
        | Some (CannotSplit (id, before, newty)) ->
          user_err_loc
            (loc,
             str"Unable to split variable " ++ Name.print id ++ str" of (reduced) type " ++
             Printer.pr_econstr_env (push_rel_context before env) !evars newty ++ str" to match a user pattern."
             ++ fnl () ++ str "Maybe unification is stuck as it cannot refine a context/section variable.")
       | None -> None))
  | [] -> (* Every clause failed for the problem, it's either uninhabited or
             the clauses are not exhaustive *)
    match find_empty (env,evars) prob.src_ctx with
    | Some (i, ctx, s) ->
      Some (List.rev prev @ clauses, (* Split (prob, i, ty, s)) *)
            Compute (prob, [], ty, REmpty (i, s)))
    | None ->
      user_err_loc (p.program_loc,
        (str "Non-exhaustive pattern-matching, no clause found for:" ++ fnl () ++
         pr_problem p env !evars prob))

and interp_clause env evars p data prev clauses' path prob
    extpats lets ty
    ((loc,lhs,rhs), used) (s, uinnacs, innacs) =
  let { src_ctx = ctx; map_inst = pats; tgt_ctx = ctx' } = prob in
  let env' = push_rel_context_eos ctx env evars in
  let get_var loc i s =
    match assoc i s with
    | PRel i -> i
    | _ -> user_err_loc (loc, str"Unbound variable " ++ Id.print i)
  in
  let () = (* Check innaccessibles are correct *)
    let check_uinnac (user, t) =
      (* let ty =
       *   let t = pat_constr t in
       *   let ty = Retyping.get_type_of env !evars t in *)
      let userc, usercty = interp_constr_in_rhs env ctx evars data None s lets (GlobConstr user) in
      match t with
      | PInac t ->
        begin match Evarconv.unify env' !evars Conversion.CONV userc t with
          | evars' -> evars := evars'
          | exception Pretype_errors.PretypeError (env, sigma, e) ->
            DAst.with_loc_val (fun ?loc _ ->
                CErrors.user_err ?loc
                  (hov 0 (str "Incompatible innaccessible pattern " ++
                          Printer.pr_econstr_env env' !evars userc ++ cut () ++
                          spc () ++ str "should be unifiable with " ++
                          Printer.pr_econstr_env env' !evars t ++ cut () ++
                          str"Unification failed with " ++
                          Himsg.explain_pretype_error env sigma e))) user
        end
      | _ ->
        let t = pat_constr t in
        let msg =
          str "Pattern " ++
          Printer.pr_econstr_env env' !evars userc ++
          spc () ++ str "is not inaccessible, but should refine pattern " ++
          Printer.pr_econstr_env env' !evars t
        in DAst.with_loc_val (fun ?loc _ -> raise (UnfaithfulSplit (loc, msg))) user
    in
    let check_innac (user, forced) =
      DAst.with_loc_val (fun ?loc user ->
      (* Allow patterns not written by the user to be forced innaccessible silently *)
      if Option.is_empty loc then ()
      else
        match user with
        | PUVar (i, _) ->
          (* If the pattern comes from a wildcard or is a variable,
             allow forcing innaccessibles too *)
          ()
        | _ ->
          let ctx, envctx, liftn, subst = env_of_rhs evars ctx env s lets in
          let forcedsubst = substnl subst 0 forced in
          CErrors.user_err ?loc
            (str "This pattern must be innaccessible and equal to " ++
             Printer.pr_econstr_env (push_rel_context ctx env) !evars forcedsubst)) user
    in
    List.iter check_uinnac uinnacs;
    List.iter check_innac innacs
  in
  match rhs with
  | Program (c,w) ->
    let (ctx, envctx, liftn, subst as letctx) = env_of_rhs evars ctx env s lets in
    let data, envctx, lets, nwheres, env', coverings, lift, subst =
      interp_wheres env ctx evars path data s lets letctx w in
    let c', ty' =
      interp_constr_in_rhs_env env evars data (lets, envctx, lift, subst)
        nwheres c (Some (Vars.lift nwheres ty)) in
    (* Compute the coverings using type information from the term using
       the where clauses *)
    let coverings = List.map (fun c -> Lazy.force c) coverings in
    let res = Compute (prob, coverings, ty', RProgram c') in
    Some res

  | Empty (loc,i) ->
    (match prove_empty (env, evars) prob.src_ctx (get_var loc i s) with
     | None -> user_err_loc (loc, str"Cannot show that " ++ Id.print i ++ str"'s type is empty")
     | Some (i, ctx, s) ->
       Some (Compute (prob, [], ty, REmpty (i, s))))

  | Refine (cs, cls) ->
    (* The refined term and its type *)
    let c, cs =
      match cs with
      | [c] -> c, []
      | c :: cs -> c, cs
      | [] -> assert false
    in
    let cconstr, cty = interp_constr_in_rhs env ctx evars data None s lets (ConstrExpr c) in

    let vars = variables_of_pats pats in
    let newctx, pats', pats'' = instance_of_pats env !evars ctx vars in
    (* revctx is a variable substitution from a reordered context to the
       current context *)
    let revctx = check_ctx_map env !evars { src_ctx = newctx; map_inst = pats'; tgt_ctx = ctx } in
    let idref = Namegen.next_ident_away (Id.of_string "refine") (Id.Set.of_list (ids_of_rel_context newctx)) in
    let refterm (* in newctx *) = mapping_constr !evars revctx cconstr in
    let refty = mapping_constr !evars revctx cty in
    let decl = make_assum (nameR idref) refty in
    let extnewctx = decl :: newctx in
    (* cmap : Δ -> ctx, cty,
       strinv associates to indexes in the strenghtened context to
       variables in the original context.
    *)
    let ty_min_fv = 
      let fvs = Int.Set.union (free_rels !evars refty) (free_rels !evars refterm) in
      match Int.Set.min_elt_opt fvs with
      | None -> 1
      | Some m -> m
      (* Forces to declare the refined variable below its type and term dependencies for well-formedness *)
    in
    (* equations_debug Pp.(fun () -> str"Moving refine variable decl to: " ++ int ty_min_fv); *)
    let tytop, tytopinv = 
      let before, after = List.chop (pred ty_min_fv) newctx in
      let newdecl' = make_assum (nameR idref) (lift (- (pred ty_min_fv)) refty) in
      let newctx = lift_rel_context 1 before @ newdecl' :: after in
      mk_ctx_map env !evars newctx 
        (PRel ty_min_fv :: List.rev (patvars_of_ctx before) @ List.rev (lift_pats ty_min_fv (patvars_of_ctx after)))
        extnewctx,
      mk_ctx_map env !evars extnewctx
        (lift_pats 1 (List.rev (patvars_of_ctx before)) @ (PRel 1 :: List.rev (lift_pats ty_min_fv (patvars_of_ctx after))))
        newctx
    in
    let refterm (* in extnewctx *) = lift 1 refterm in
    equations_debug Pp.(fun () -> str" Strenghtening variable decl: " ++ pr_context_map env !evars tytop);
    equations_debug Pp.(fun () -> str" Strenghtening variable decl inv: " ++ pr_context_map env !evars tytopinv);
    let cmap, strinv = new_strengthen env !evars tytop.src_ctx 1 refterm in
    let cmap = compose_subst env ~sigma:!evars cmap tytop in
    let strinv = compose_subst env ~sigma:!evars tytopinv strinv in
    let strinv_map = List.map_i (fun i -> function (PRel j) -> i, j | _ -> assert false) 1 strinv.map_inst in
    equations_debug Pp.(fun () -> str" Strenghtening: " ++ pr_context_map env !evars cmap);
    equations_debug Pp.(fun () -> str" Strenghtening inverse: " ++ pr_context_map env !evars strinv);
    let idx_of_refined = destPRel (CList.hd cmap.map_inst) in
    equations_debug Pp.(fun () -> str" idx_of_refined: " ++ int idx_of_refined);
    let cmap =
      abstract_term_in_context env !evars idx_of_refined (mapping_constr !evars cmap refterm) cmap
    in
    equations_debug Pp.(fun () -> str" Strenghtening + abstraction: " ++ pr_context_map env !evars cmap);
    let newprob_to_lhs =
      let inst_refctx = set_in_ctx idx_of_refined (mapping_constr !evars cmap refterm) cmap.src_ctx in
      let str_to_new = {
        src_ctx = inst_refctx;
        map_inst = specialize_pats !evars cmap.map_inst (lift_pats 1 pats');
        tgt_ctx = newctx;
      } in
      equations_debug Pp.(fun () -> str" Strenghtening + abstraction + instantiation: " ++ pr_context_map env !evars str_to_new);
      compose_subst env ~sigma:!evars str_to_new revctx
    in	
    equations_debug Pp.(fun () -> str" Strenghtening + abstraction + instantiation: " ++ pr_context_map env !evars newprob_to_lhs);

    let newprob = 
      let ctx = cmap.src_ctx in
      let pats = 
        rev_map (fun c -> 
            let idx = destRel !evars c in
            (* find out if idx in ctx should be hidden depending
               on its use in newprob_to_lhs *)
            if List.exists (function PHide idx' -> idx == idx' | _ -> false)
                newprob_to_lhs.map_inst then
              PHide idx
            else PRel idx) (rels_of_ctx ctx) in
      { src_ctx = ctx; map_inst = pats; tgt_ctx = ctx }
    in
    let newty =
      let env' = push_rel_context extnewctx env in
      let refterm  = Tacred.simpl env' !evars refterm in
      subst_term !evars refterm
        (Tacred.simpl env'
           !evars (lift 1 (mapping_constr !evars revctx ty)))
    in
    let newty = mapping_constr !evars cmap newty in
    (* The new problem forces a reordering of patterns under the refinement
       to make them match up to the context map. *)
    let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv_map in
    let vars' = List.rev_map snd sortinv in
    let cls =
      match cs with
      | [] -> cls
      | _ :: _ ->
        [Pre_clause (loc, lhs @ [DAst.make ?loc (PUVar (idref, Generated))], Some (Refine (cs, cls)))]
    in
    let rec cls' n cls =
      let next_unknown =
        let str = Id.of_string "unknown" in
        let i = ref (-1) in fun () ->
          incr i; add_suffix str (string_of_int !i)
      in
      List.map_filter (fun (Pre_clause (loc, lhs, rhs)) ->
        let oldpats, newpats = List.chop (List.length lhs - n) lhs in
        let newref, nextrefs =
          match newpats with hd :: tl -> hd, tl | [] -> assert false
        in
        match matches_user env prob (extpats @ oldpats) with
        | UnifSuccess (s, alias) ->
          (* A substitution from the problem variables to user patterns and
             from user pattern variables to patterns instantiating problem variables. *)
          let newlhs =
            List.map_filter
              (fun i ->
                 if i == 1 then Some newref
                 else
                 if List.exists (fun (i', b) -> i' == pred i && b) vars then None
                 else
                   try Some (DAst.make (List.assoc (pred i) s))
                   with Not_found -> (* The problem is more refined than the user vars*)
                     Some (DAst.make (PUVar (next_unknown (), Generated))))
              vars'
          in
          let newrhs = match rhs with
            | Some (Refine (cs', cls)) -> Some (Refine (cs', cls' (List.length cs' + n) cls))
            | _ -> rhs
          in
          Some (Pre_clause (loc, rev newlhs @ nextrefs, newrhs))
        | _ ->
          CErrors.user_err ?loc
            (str "Non-matching clause in with subprogram:" ++ fnl () ++ int n ++
             str"Problem is " ++ spc () ++ pr_context_map env !evars prob ++ fnl () ++
             str"And the user patterns are: " ++ spc () ++
             pr_user_pats env !evars lhs)) cls
    in
    let cls' = cls' 1 cls in
    let strength_app =
      let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv_map in
      let args =
        List.map (fun (i, j) (* i variable in strengthened context, 
                                j variable in the original one *) -> 
                   if j == 1 then (cconstr)
                   else let (var, _) = List.nth vars (pred (pred j)) in
                     mkRel var) sortinv
      in args
    in
    let strength_app = List.map_filter (fun t ->
        if isRel !evars t then
          let i = destRel !evars t in
          let decl = List.nth prob.src_ctx (pred i) in
          if Context.Rel.Declaration.is_local_def decl then None
          else Some t
        else Some t) strength_app
    in
    let path' = path in
    let lets' =
      let letslen = length lets in
      let _, ctxs, _ = lets_of_ctx env ctx evars s in
      let newlets = (lift_rel_context (succ letslen) ctxs)
                    @ (lift_rel_context 1 lets)
      in specialize_rel_context !evars cmap.map_inst newlets
    in
    let clauses' = List.mapi (fun i x -> x, (succ i, 0)) cls' in
    match covering_aux env evars p data [] clauses' path' newprob [] lets' newty with
    | None ->
      errorlabstrm
        (str "Unable to build a covering for with subprogram:" ++ fnl () ++
         pr_problem p env !evars newprob ++ fnl () ++
         str "And clauses: " ++ pr_preclauses env !evars cls')
    | Some (clauses, s) ->
      let () = check_unused_clauses env !evars clauses in
      let term, _ = term_of_tree env evars (ESorts.make p.program_sort) s in
      let info =
        { refined_obj = (idref, cconstr, cty);
          refined_rettyp = ty;
          refined_arg = refine_arg idx_of_refined cmap.src_ctx;
          refined_path = path';
          refined_term = term;
          refined_filter = None;
          refined_args = strength_app;
          (* refined_args = (mkEvar (evar, secvars), strength_app); *)
          refined_revctx = revctx;
          refined_newprob = newprob;
          refined_newprob_to_lhs = newprob_to_lhs;
          refined_newty = newty }
      in  Some (Refined (prob, info, s))
(* else  *)
(*   anomaly ~label:"covering" *)
(*     (str "Found overlapping clauses:" ++ fnl () ++ pr_clauses env (map fst prevmatch) ++ *)
(*        spc () ++ str"refining" ++ spc () ++ pr_context_map env prob) *)

and interp_wheres env0 ctx evars path data s lets
    (ctx, envctx, liftn, subst)
    (w : (pre_prototype * pre_equation list) list * Vernacexpr.notation_declaration list) =
  let notations = snd w in
  let aux (data,lets,nlets,coverings,env)
      (((loc,id),udecl,nested,b,t,reca),clauses as eqs) =

    let is_rec = is_recursive id ([eqs], notations) in
    let p = interp_arity env evars ~poly:false ~is_rec ~with_evars:true notations eqs in
    let clauses = List.map (interp_eqn env !evars (data.notations @ notations) p ~avoid:Id.Set.empty) clauses in
    let sigma, p = adjust_sign_arity env !evars p clauses in
    let () = evars := sigma in

    let pre_type = Syntax.program_type p in
    let rel, fixp = 
      if is_rec then make_fix_proto env !evars pre_type 
      else Retyping.relevance_of_type env !evars pre_type, pre_type in
    let fixdecls = [Context.Rel.Declaration.LocalAssum (make_annot (Name id) rel, fixp)] in
    let rec_type = compute_rec_type data.rec_type [p] in
    let rec_data = {data with rec_type; fixdecls} in
    let p, problem, arity, extpats, rec_info =
      compute_rec_data env evars rec_data lets subst p in
    let intenv = Constrintern.compute_internalization_env ~impls:data.intenv
        env !evars Constrintern.Recursive [id] [pre_type] [p.program_impls]
    in
    let rec_data = { rec_data with intenv; notations = data.notations @ notations } in
    let data = { data with intenv; notations = data.notations @ notations } in
    let path = id :: path in

    let where_args = extended_rel_list 0 lets in
    let where_args = List.map (substnl subst nlets) where_args in
    let w' program =
      {where_program = program; where_program_orig = p;
       where_program_args = where_args;
       where_path = path;
       where_orig = path;
       where_context_length = List.length extpats;
       where_type = pre_type }
    in
    let program, term =
      match t with
      | Some ty (* non-delayed where clause, compute term right away *) ->
        let splitting = covering env0 evars p rec_data clauses path problem extpats arity in
        let program = make_single_program env0 evars data.flags p problem splitting rec_info in
        Lazy.from_val (w' program), program.program_term
      | None ->
        let relty = Syntax.program_type p in
        let src = (loc, Evar_kinds.(QuestionMark {
            qm_obligation=Define false;
            qm_name=Name id;
            qm_record_field=None;
          })) in
        let sigma, term = Equations_common.new_evar env0 !evars ~src relty in
        let () = evars := sigma in
        let ev = destEvar !evars term in
        let cover () =
          let splitting = covering env0 evars p rec_data clauses path problem extpats arity in
          let program = make_single_program env0 evars data.flags p problem splitting rec_info in
          evars := Evd.define (fst ev) program.program_term !evars; w' program
        in
        Lazy.from_fun cover, term
    in
    let decl = make_def (nameR id) (Some (applistc term where_args)) pre_type in
    (data, decl :: lets, succ nlets, program :: coverings,
     push_rel decl envctx)
  in
  let (data, lets, nlets, coverings, envctx') =
    List.fold_left aux (data, ctx, 0, [], push_rel_context ctx env0) (fst w)
  in (data, envctx, lets, nlets, push_rel_context ctx env0, coverings, liftn, subst)

and covering ?(check_unused=true) env evars p data (clauses : pre_clause list)
    path prob extpats ty =
  let clauses = (List.mapi (fun i x -> (x,(succ i,0))) clauses) in
  (*TODO eta-expand clauses or type *)
  match covering_aux env evars p data [] clauses path prob extpats [] ty with
  | Some (clauses, cov) ->
    let () = if check_unused then check_unused_clauses env !evars clauses in
    cov
  | None ->
    errorlabstrm
      (str "Unable to build a covering for:" ++ fnl () ++
       pr_problem p env !evars prob)

let program_covering env evd data p clauses =
  let clauses = List.map (interp_eqn (push_rel_context data.fixdecls env) !evd
    data.notations p ~avoid:Id.Set.empty) clauses in
  let sigma, p = adjust_sign_arity env !evd p clauses in
  let () = evd := sigma in
  let p', prob, arity, extpats, rec_node = compute_rec_data env evd data [] [] p in
  let splitting =
    covering env evd p data clauses [p.program_id] prob extpats arity
  in (p', prob, splitting, rec_node)

let coverings env evd data programs equations =
  let splittings = List.map2 (program_covering env evd data) programs equations in
  make_programs env evd data.flags splittings
