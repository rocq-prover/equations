(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Principles derived from equation definitions. *)

open Names
open Context
open Equations_common
open Syntax
open Context_map
open Splitting
open Principles_proofs

type statement = EConstr.constr * EConstr.types option
type statements = statement list

type recursive = bool

type node_kind =
  | Regular
  | Refine
  | Where
  | Nested of recursive

let kind_of_prog p =
  match p.Syntax.program_rec with
  | Some (Structural (NestedOn _)) -> Nested true
  | Some (Structural NestedNonRec) -> Nested false
  | _ -> Regular

let regular_or_nested = function
  | Regular | Nested _ -> true
  | _ -> false

let regular_or_nested_rec = function
  | Regular -> true
  | Nested r -> true
  | _ -> false

let nested = function Nested _ -> true | _ -> false

let pi1 (x,_,_) = x
let pi2 (_,y,_) = y

(** Objects to keep information about equations *)

let cache_rew_rule (base, gr, l2r) =
  let gr, ((qvars, univs), csts) = UnivGen.fresh_global_instance (Global.env()) gr in
  let () = if not (Sorts.QVar.Set.is_empty qvars) then
      CErrors.user_err Pp.(str "Sort polymorphic autorewrite not supported.")
  in
  let gru = gr, ((qvars, univs), csts) in
  Autorewrite.add_rew_rules
    ~locality:Hints.(if Global.sections_are_opened() then Local else SuperGlobal)
    base
    [CAst.make (gru, true, None)]

let inRewRule =
  let open Libobject in
  (* Object just to provide discharge *)
  declare_object
    { (default_object "EQUATIONS_REWRITE_RULE") with
      cache_function = (fun obj -> cache_rew_rule obj);
      discharge_function = (fun x -> Some x);
      classify_function = (fun _ -> Dispose)
    }

let add_rew_rule ~l2r ~base ref = Lib.add_leaf (inRewRule (base,ref,l2r))

let cache_opacity cst =
  Global.set_strategy (Conv_oracle.EvalConstRef cst) Conv_oracle.Opaque

let subst_opacity (subst, cst) =
  let gr' = Mod_subst.subst_constant subst cst in
  gr'

let inOpacity =
  let open Libobject in
  let obj =
    (* We allow discharging rewrite rules *)
    superglobal_object "EQUATIONS_OPACITY"
      ~cache:cache_opacity
      ~subst:(Some subst_opacity)
      ~discharge:(fun x -> Some x)
  in
  declare_object @@ obj

let match_arguments sigma l l' =
  let rec aux i =
    if i < Array.length l' then
      if i < Array.length l then
        if EConstr.eq_constr sigma l.(i) l'.(i) then
          i :: aux (succ i)
        else aux (succ i)
      else aux (succ i)
    else [i]
  in aux 0

let filter_arguments f l =
  let rec aux i f l =
    match f, l with
    | n :: f', a :: l' ->
       if i < n then aux (succ i) f l'
       else if i = n then
         a :: aux (succ i) f' l'
       else assert false
    | _, _ -> l
  in aux 0 f l

module CMap = Map.Make(Termops.ConstrData)

let clean_rec_calls sigma (hyps, c) =
  let open Context.Rel.Declaration in
  (* Remove duplicate induction hypotheses under contexts *)
  let under_context, hyps =
    CMap.partition (fun ty n -> Constr.isProd ty || Constr.isLetIn ty) hyps
  in
  let hyps =
    CMap.fold (fun ty n hyps ->
      let ctx, concl = Term.decompose_prod_decls ty in
      let len = List.length ctx in
      if Vars.noccur_between 1 len concl then
          if CMap.mem (Constr.lift (-len) concl) hyps then hyps
          else CMap.add ty n hyps
        else CMap.add ty n hyps)
      under_context hyps
  in
  (* Sort by occurrence *)
  let elems = List.sort (fun x y -> Int.compare (snd x) (snd y)) (CMap.bindings hyps) in
  let (size, ctx) =
    List.fold_left (fun (n, acc) (ty, _) ->
    (succ n, LocalAssum (EConstr.nameR (Id.of_string "Hind"), EConstr.Vars.lift n (EConstr.of_constr ty)) :: acc))
    (0, []) elems
  in
  (ctx, size, EConstr.Vars.lift size (EConstr.of_constr c))

let head c = fst (Constr.decompose_app c)

let rec is_applied_to_structarg f is_rec lenargs =
  match is_rec with
  | Some (Guarded ids) :: rest -> begin
     try
       let kind =
         CList.find_map_exn (fun (f', k) -> if Id.equal f f' then Some k else None) ids
       in
       match kind with
       | MutualOn (Some (idx,_)) | NestedOn (Some (idx,_)) -> Some (lenargs > idx)
       | MutualOn None | NestedOn None | NestedNonRec -> Some true
     with Not_found -> is_applied_to_structarg f rest lenargs
    end
  | _ :: rest -> is_applied_to_structarg f rest lenargs
  | [] -> None

let is_user_obl sigma user_obls f =
  match EConstr.kind sigma f with
  | Constr.Const (c, u) -> Id.Set.mem (Constant.label c) user_obls
  | _ -> false

let cmap_map f c =
  CMap.fold (fun ty n hyps -> CMap.add (f ty) n hyps) c CMap.empty

let cmap_union g h =
  CMap.merge (fun ty n m ->
    match n, m with
    | Some n, Some m -> Some (min n m)
    | Some _, None -> n
    | None, Some _ -> m
    | None, None -> None) g h

let cmap_add ty n h =
  cmap_union (CMap.singleton ty n) h


let subst_telescope cstr ctx =
  let (_, ctx') = List.fold_left
    (fun (k, ctx') decl ->
      (succ k, (Context.Rel.Declaration.map_constr (Vars.substnl [cstr] k) decl) :: ctx'))
    (0, []) ctx
  in List.rev ctx'

let substitute_args args ctx =
  let open Context.Rel.Declaration in
  let rec aux ctx args =
    match args, ctx with
    | a :: args, LocalAssum _ :: ctx -> aux (subst_telescope a ctx) args
    | _ :: _, LocalDef (na, b, t) :: ctx -> aux (subst_telescope b ctx) args
    | [], ctx -> List.rev ctx
    | _, [] -> assert false
  in aux (List.rev ctx) args

let drop_last_n n l =
  let l = List.rev l in
  let l = CList.skipn n l in
  List.rev l

let find_rec_call is_rec sigma protos f args =
  let fm (fhead,(f',filter), alias, idx, sign, arity) =
    if Constr.equal (EConstr.Unsafe.to_constr fhead) f then
      let f' = fst (Constr.destConst f) in
      match is_applied_to_structarg (Names.Constant.label f') is_rec
              (List.length args) with
      | Some true | None ->
        let signlen = List.length sign in
        let indargs = filter_arguments filter args in
        let sign, args =
          if signlen <= List.length indargs then
            (* Exact or extra application *)
            let indargs, rest = CList.chop signlen indargs in
            let fargs = drop_last_n (List.length rest) args in
            [], (fargs, indargs, rest)
          else
            (* Partial application *)
            let sign = List.map EConstr.Unsafe.to_rel_decl sign in
            let sign = substitute_args indargs sign in
            let signlen = List.length sign in
            let indargs = List.map (Constr.lift signlen) indargs @ Context.Rel.instance_list Constr.mkRel 0 sign in
            let fargs = List.map (Constr.lift signlen) args @ Context.Rel.instance_list Constr.mkRel 0 sign in
            sign, (fargs, indargs, [])
        in
        Some (idx, arity, filter, sign, args)
      | Some false -> None
    else
      match alias with
      | Some (f',argsf) ->
        let signlen = List.length sign in        
        let f', args' = EConstr.decompose_app sigma f' in
        let f' = EConstr.Unsafe.to_constr f' in
        if Constr.equal (head f') f then
          let sign, args = 
            if signlen <= List.length args then
              (* Exact or extra application *)
              let indargs, rest = CList.chop signlen args in
              let fargs = drop_last_n (List.length rest) args in
              [], (fargs, indargs, rest)
            else
              (* Partial application *)
              let sign = List.map EConstr.Unsafe.to_rel_decl sign in
              let sign = substitute_args args sign in
              let signlen = List.length sign in
              let indargs = List.map (Constr.lift signlen) args @ Context.Rel.instance_list Constr.mkRel 0 sign in
              let fargs = List.map (Constr.lift signlen) args @ Context.Rel.instance_list Constr.mkRel 0 sign in
              sign, (fargs, indargs, [])
          in
          Some (idx, arity, argsf, sign, args)
        else None
      | None -> None
  in
  CList.find_map fm protos

let filter_arg i filter =
  let rec aux f =
    match f with
    | i' :: _ when i < i' -> true
    | i' :: _ when i = i' -> false
    | i' :: is -> aux is
    | [] -> false
  in aux filter

let abstract_rec_calls sigma user_obls ?(do_subst=true) is_rec len protos c =
  let proto_fs = List.map (fun (_,(f,args), _, _, _, _) -> f) protos in
  let occ = ref 0 in
  let rec aux n env hyps c =
    let open Constr in
    match kind c with
    | Lambda (na,t,b) ->
      let hyps',b' = aux (succ n) ((na,None,t) :: env) CMap.empty b in
      let hyps' = cmap_map (fun ty -> mkProd (na, t, ty)) hyps' in
        cmap_union hyps hyps', c

    (* | Cast (_, _, f) when is_comp f -> aux n f *)

    | LetIn (na,b,t,body) ->
      let hyps',b' = aux n env hyps b in
      let hyps'',body' = aux (succ n) ((na,Some b,t) :: env) CMap.empty body in
        cmap_union hyps' (cmap_map (fun ty -> Constr.mkLetIn (na,b,t,ty)) hyps''), c

    | Prod (na, d, c) when Vars.noccurn 1 c  ->
      let hyps',d' = aux n env hyps d in
      let hyps'',c' = aux n env hyps' (Vars.subst1 mkProp c) in
        hyps'', mkProd (na, d', lift 1 c')

    | Case (ci, u, pms, p, iv, c, brs) ->
      let (ci, p, iv, c, brs) = Inductive.expand_case (Global.env ()) (ci, u, pms, p, iv, c, brs) in
      let hyps', c' = aux n env hyps c in
      let hyps' = Array.fold_left (fun hyps br -> fst (aux n env hyps br)) hyps' brs in
      let case' = mkCase (Inductive.contract_case (Global.env ()) (ci, p, iv, c', brs)) in
        hyps', EConstr.Unsafe.to_constr (EConstr.Vars.substnl proto_fs (succ len) (EConstr.of_constr case'))

    | Proj (p, r, c) ->
      let hyps', c' = aux n env hyps c in
        hyps', mkProj (p, r, c')

    | _ ->
      let f', args = decompose_app c in
      if not (is_user_obl sigma user_obls (EConstr.of_constr f')) then
        (match find_rec_call is_rec sigma protos f' (Array.to_list args) with
         | Some (i, arity, filter, sign, (fargs', indargs', rest)) ->
           let hyps =
             CArray.fold_left_i
               (fun i hyps arg ->
                  if filter_arg i filter then hyps
                  else let hyps', arg' = aux n env hyps arg in hyps')
               hyps args
           in
           let fargs' = Constr.mkApp (f', Array.of_list fargs') in
           let result = Term.it_mkLambda_or_LetIn fargs' sign in
           let hyp =
             Term.it_mkProd_or_LetIn
               (Constr.mkApp (mkApp (mkRel (i + 1 + len + n + List.length sign), Array.of_list indargs'),
                              [| Term.applistc (lift (List.length sign) result)
                                   (Context.Rel.instance_list mkRel 0 sign) |]))
               sign
           in
           let hyps = cmap_add hyp !occ hyps in
           let () = incr occ in
           let c' = Term.applist (result, rest) in
           hyps, c'
         | None ->
           let hyps =
             Array.fold_left (fun hyps arg -> let hyps', arg' = aux n env hyps arg in
                               hyps')
               hyps args
           in
           hyps, mkApp (f', args))
      else
        let c' =
          if do_subst then (EConstr.Unsafe.to_constr (EConstr.Vars.substnl proto_fs (len + n) (EConstr.of_constr c)))
          else c
        in hyps, c'
  in clean_rec_calls sigma (aux 0 [] CMap.empty (EConstr.Unsafe.to_constr c))

open EConstr

let subst_app sigma f fn c =
  let rec aux n c =
    match kind sigma c with
    | Constr.App (f', args) when eq_constr sigma f f' ->
      let args' = Array.map (map_with_binders sigma succ aux n) args in
      fn n f' args'
    | Constr.Var _ when eq_constr sigma f c ->
       fn n c [||]
    | _ -> map_with_binders sigma succ aux n c
  in aux 0 c

let subst_comp_proj sigma f proj c =
  subst_app sigma proj (fun n x args ->
    mkApp (f, if Array.length args > 0 then Array.sub args 0 (Array.length args - 1) else args))
    c

(* Substitute occurrences of [proj] by [f] in the splitting. *)
let subst_comp_proj_split sigma f proj s =
  map_split (subst_comp_proj sigma f proj) s

let is_ind_assum env sigma ind b =
  let _, concl = decompose_prod_decls sigma b in
  let t, _ = decompose_app sigma concl in
  if isInd sigma t then
    let (ind', _), _ = destInd sigma t in
    Environ.QMutInd.equal env ind' ind
  else false

let clear_ind_assums env sigma ind ctx =
  let rec clear_assums c =
    match kind sigma c with
    | Constr.Prod (na, b, c) ->
       if is_ind_assum env sigma ind b then
         (assert(not (Termops.dependent sigma (mkRel 1) c));
          clear_assums (Vars.subst1 mkProp c))
       else mkProd (na, b, clear_assums c)
    | Constr.LetIn (na, b, t, c) ->
        mkLetIn (na, b, t, clear_assums c)
    | _ -> c
  in map_rel_context clear_assums ctx

let type_of_rel k ctx =
  Vars.lift k (get_type (List.nth ctx (pred k)))

open Vars

let compute_elim_type env evd user_obls is_rec protos k leninds
                      ind_stmts all_stmts sign app elimty =
  let ctx, arity = decompose_prod_decls !evd elimty in
  let lenrealinds =
    List.length (List.filter (fun (_, (_,_,_,_,_,_,_,(kind,_)),_) -> regular_or_nested_rec kind) ind_stmts) in
  let newctx =
    if lenrealinds == 1 then CList.skipn (List.length sign + 2) ctx
    else ctx
  in
  (* Assumes non-dep mutual eliminator of the graph *)
  let newarity =
    if lenrealinds == 1 then
      it_mkProd_or_LetIn (Vars.substl [mkProp; app] arity) sign
    else
      let clean_one a sign fn =
        let ctx, concl = decompose_prod_decls !evd a in
        let newctx = CList.skipn 2 ctx in
        let newconcl = Vars.substl [mkProp; mkApp (fn, extended_rel_vect 0 sign)] concl in
        it_mkProd_or_LetIn newconcl newctx
      in
      let rec aux arity ind_stmts =
        match kind !evd arity, ind_stmts with
        | _, (i, ((fn, _), _, _, sign, ar, _, _, ((Where | Refine), cut)), _) :: stmts ->
           aux arity stmts
        | Constr.App (conj, [| arity; rest |]),
          (i, ((fn, _), _, _, sign, ar, _, _, (refine, cut)), _) :: stmts ->
           mkApp (conj, [| clean_one arity sign fn ; aux rest stmts |])
        | _, (i, ((fn, _), _, _, sign, ar, _, _, _), _) :: stmts ->
           aux (clean_one arity sign fn) stmts
        | _, [] -> arity
      in aux arity ind_stmts
  in
  let newctx' = clear_ind_assums env !evd k newctx in
  if leninds == 1 then List.length newctx', it_mkProd_or_LetIn newarity newctx' else
  let sort = fresh_sort_in_quality_or_set evd UnivGen.QualityOrSet.qtype in
  let methods, preds = CList.chop (List.length newctx - leninds) newctx' in
  let ppred, preds = CList.sep_last preds in
  let newpredfn i d (idx, (f', alias, path, sign, arity, pats, args, (refine, cut)), _) =
    if refine != Refine then d else
    let (n, b, t) = to_tuple d in
    let signlen = List.length sign in
    let ctx = of_tuple (anonR, None, arity) :: sign in
    let app =
      let argsinfo =
        match args with
        | Some (c, (arg, _argnolets)) ->
          let idx = signlen - arg + 1 in (* lift 1, over return value *)
          let ty = Vars.lift (idx (* 1 for return value *))
              (get_type (List.nth sign (pred (pred idx))))
          in
          Some (idx, ty, lift 1 c, mkRel idx)
        | None -> None
      in
      let transport = get_efresh logic_eq_case evd in
      let transport ty x y eq c cty =
        mkApp (transport,
               [| ty;
                  mkLambda (nameR (Id.of_string "abs"), ty,
                            Termops.replace_term !evd (Vars.lift 1 x) (mkRel 1) (Vars.lift 1 cty));
                  x; y; eq; (* equality *) c |])
      in
      let lenargs, pargs, subst =
        match argsinfo with
        | None -> 0, List.map (lift 1) pats, []
        | Some (i, ty, c, rel) ->
          let lenargs = 1 in
          let pargs, subst =
            List.fold_right
              (fun t (pargs, subst) ->
            let rel = lift lenargs rel in
            let default () =
              (* for equalities + return value *)
              let t' = lift (lenargs+1) (t) in
              let t' = Termops.replace_term !evd (lift (lenargs) c) rel t' in
              (t' :: pargs, subst)
            in
            match EConstr.kind !evd t with
            | Constr.Rel k ->
              let tty = lift (lenargs+1) (type_of_rel k sign) in
              if Termops.dependent !evd rel tty then
                let tr =
                  if isRel !evd c then lift (lenargs+1) t
                  else
                    transport (lift lenargs ty) rel (lift lenargs c)
                      (mkRel 1) (lift (lenargs+1) (t)) tty
                in
                let t' =
                  if isRel !evd c then lift (lenargs+3) (t)
                  else transport (lift (lenargs+2) ty)
                      (lift 2 rel)
                      (mkRel 2)
                      (mkRel 1) (lift (lenargs+3) (t)) (lift 2 tty)
                in (tr :: pargs, (k, t') :: subst)
              else default ()
            | _ -> default ()) pats ([], [])
          in lenargs, pargs, subst
      in
      let result =
        match argsinfo with
        | None -> mkRel 1
        | Some (i, ty, c, rel) ->
          (* Lift over equality *)
          let arity = lift 1 arity in
          (* equations_debug Pp.(fun () -> str"Testing dependency of "  ++ Printer.pr_econstr_env env !evd arity ++
           *                               str" in " ++ int i); *)
          let replace_term t tr acc =
            (* equations_debug Pp.(fun () -> str"Replacing term "  ++ Printer.pr_econstr_env env !evd t ++
             *                               str" by " ++ Printer.pr_econstr_env env !evd tr ++ str " in " ++
             *                               Printer.pr_econstr_env env !evd acc); *)
            Termops.replace_term !evd t tr acc
          in
          if Termops.dependent !evd (mkRel i) arity then
            let acc = mkRel 2 in (* Under refine equality, reference to inner result of refine *)
            let pred = lift 3 arity in (* Under result binding,
                                          refine equality, and transport by it: abstracted endpoint and eq *)
            (* equations_debug Pp.(fun () -> str"Refined constrs "  ++
             *                               prlist_with_sep spc (fun (rel, t) ->
             *                                   Printer.pr_econstr_env env !evd (mkRel rel) ++ str " -> " ++
             *                                   Printer.pr_econstr_env env !evd t) subst); *)
            (* The predicate is dependent on the refined variable. *)
            let eqty =
              mkEq env evd (lift 2 ty) (mkRel 1) (lift 2 rel)
            in
            let pred' =
              let absterm = replace_term (mkRel (i + 3)) (mkRel 2) pred in
              (* equations_debug Pp.(fun () -> str"Abstracted term "  ++ Printer.pr_econstr_env env !evd absterm); *)
              List.fold_left
                (fun acc (t, tr) -> replace_term (mkRel (t + 4)) tr acc)
                absterm subst
            in
            let app =
              if noccurn !evd 1 pred' then
                let transport = get_efresh logic_eq_case evd in
                mkApp (transport,
                       [| lift lenargs ty;
                          mkLambda (nameR (Id.of_string "refine"), lift lenargs ty, subst1 mkProp pred');
                          lift lenargs rel; lift lenargs c; mkRel 1 (* equality *); acc |])

              else
                let transportd = get_efresh logic_eq_elim evd in
                mkApp (transportd,
                       [| lift lenargs ty; lift lenargs rel;
                          mkLambda (nameR (Id.of_string "refine"), lift lenargs ty,
                                    mkLambda (nameR (Id.of_string "refine_eq"), eqty, pred'));
                          acc; (lift lenargs c); mkRel 1 (* equality *) |])
            in app
          else mkRel 2
      in
      let ppath = (* The preceding P *)
        match path with
        | _ :: path ->
          (let res =
             list_find_map_i (fun i' (_, (_, _, path', _, _, _, _, _), _) ->
                 if eq_path path' path then Some (idx + 1 - i')
                 else None) 1 ind_stmts
           in match res with None -> assert false | Some i -> i)
        | _ -> assert false
      in
      let papp =
        applistc (lift (succ signlen + lenargs) (mkRel ppath))
                 pargs
      in
      let papp = applistc papp [result] in
      let refeqs = Option.map (fun (i, ty, c, rel) -> mkEq env evd ty c rel) argsinfo in
      let app c =
        match refeqs with
        | Some eqty -> mkProd (nameR (Id.of_string "Heq"), eqty, c)
        | None -> c
      in
      let indhyps =
        match args with
        | Some (c, _) ->
          let hyps, hypslen, c' =
            abstract_rec_calls !evd user_obls ~do_subst:false
              is_rec signlen protos (Reductionops.nf_beta env !evd (lift 1 c))
          in
          let lifthyps = lift_rel_contextn (signlen + 2) (- (pred i)) hyps in
          lifthyps
        | None -> []
      in
        it_mkLambda_or_LetIn
          (app (it_mkProd_or_clean env !evd (lift (List.length indhyps) papp)
                                   (lift_rel_context lenargs indhyps)))
          ctx
    in
    let ty = it_mkProd_or_LetIn sort ctx in
    of_tuple (n, Some app, ty)
  in
  let newpreds = CList.map2_i newpredfn 1 preds (List.rev (List.tl ind_stmts)) in
  let skipped, methods' = (* Skip the indirection methods due to refinements,
                              as they are trivially provable *)
    let rec aux stmts meths n meths' =
      match stmts, meths with
      | (Refine, _, _, _) :: stmts, decl :: decls ->
         aux stmts (Equations_common.subst_telescope mkProp decls) (succ n) meths'
      | (_, _, _, None) :: stmts, decls -> (* Empty node, no constructor *)
         aux stmts decls n meths'
      | (_, _, _, _) :: stmts, decl :: decls ->
         aux stmts decls n (decl :: meths')
      | [], [] -> n, meths'
      | [], decls -> n, List.rev decls @ meths'
      | (_, _, _, Some _) :: stmts, [] ->
        anomaly Pp.(str"More statemsnts than declarations while computing eliminator")
    in aux all_stmts (List.rev methods) 0 []
  in
  let ctx = methods' @ newpreds @ [ppred] in
  let elimty = it_mkProd_or_LetIn (lift (-skipped) newarity) ctx in
  let undefpreds = List.length (List.filter (fun decl -> Option.is_empty (get_value decl)) newpreds) in
  let nargs = List.length methods' + undefpreds + 1 in
  nargs, elimty

let replace_vars_context sigma inst ctx =
  List.fold_right
    (fun decl (k, acc) ->
      let decl' = map_rel_declaration (substn_vars sigma k inst) decl in
      (succ k, decl' :: acc))
    ctx (1, [])

let pr_where env sigma ctx ({where_type} as w) =
  let open Pp in
  let envc = Environ.push_rel_context ctx env in
  Printer.pr_econstr_env envc sigma (where_term w) ++ fnl () ++
    str"where " ++ Names.Id.print (where_id w) ++ str" : " ++
    Printer.pr_econstr_env envc sigma where_type ++
    str" := " ++ fnl () ++
    Context_map.pr_context_map env sigma w.where_program.program_prob ++ fnl () ++
    pr_splitting env sigma w.where_program.program_splitting

let where_instance w =
  List.map (fun w -> where_term w) w

let arguments sigma c = snd (decompose_app sigma c)

let unfold_constr sigma c =
  Tactics.unfold_in_concl [(Locus.OnlyOccurrences [1], Evaluable.EvalConstRef (fst (destConst sigma c)))]

let extend_prob_ctx delta map =
  { src_ctx = delta @ map.src_ctx;
    map_inst = Context_map.lift_pats (List.length delta) map.map_inst;
    tgt_ctx = map.tgt_ctx }

let map_proto evd recarg f ty =
  match recarg with
  | Some recarg ->
     let lctx, ty' = decompose_prod_decls evd ty in
     (* Feedback.msg_debug Pp.(str"map_proto: " ++ Printer.pr_econstr_env (Global.env()) evd ty ++ str" recarg = " ++ int recarg); *)
     let app =
       let args = Termops.rel_list 0 (List.length lctx) in
       let before, after =
         if recarg == -1 then CList.drop_last args, []
         else let bf, after = CList.chop recarg args in
              bf, List.tl after
       in
       applistc (lift (List.length lctx) f) (before @ after)
     in
     it_mkLambda_or_LetIn app lctx
  | None -> f

type rec_subst = (Names.Id.t * (int option * EConstr.constr)) list

let cut_problem evd s ctx =
  (* From Γ, x := t, D |- id_subst (G, x, D) : G, x : _, D
     to oΓ, D[t] |- id_subst (G, D) | G[
     ps, prec, ps' : Δ, rec, Δ',
     and s : prec -> Γ |- t : rec
     build
     Γ |- ps, ps' : Δ, Δ'[prec/rec] *)
  let rec fn s ctxm =
    match s with
    | [] -> ctxm
    | (id, (recarg, term)) :: s ->
      try
        let { src_ctx = ctxl; map_inst = pats; tgt_ctx = ctxr } = ctxm in
        let rel, _, ty = Termops.lookup_rel_id id ctxr in
        let fK = map_proto evd recarg term (lift rel ty) in
        let ctxr' = subst_in_ctx rel fK ctxr in
        let left, right = CList.chop (pred rel) pats in
        let right' = List.tl right in
        let s' = List.map (fun (id, (recarg, t)) -> id, (recarg, substnl [fK] rel t)) s in
        fn s' { src_ctx = ctxl; map_inst = List.append left right'; tgt_ctx = ctxr' }
      with Not_found -> fn s ctxm
  in fn s (id_subst ctx)

let subst_rec env evd cutprob s lhs =
  let ctx = lhs.src_ctx in
  let subst =
    List.fold_left (fun lhs' (id, (recarg, b)) ->
    let ctx = lhs'.src_ctx in
    try let rel, _, ty = Termops.lookup_rel_id id ctx in
       (* Feedback.msg_debug Pp.(str"lhs': " ++ pr_context_map env evd lhs');       *)
        let fK = map_proto evd recarg (mapping_constr evd lhs b) (lift rel ty) in
        (* Feedback.msg_debug Pp.(str"fk: " ++ Printer.pr_econstr_env (push_rel_context ctx env) evd fK); *)
        let substf = single_subst env evd rel (PInac fK) ctx in
        (* ctx[n := f] |- _ : ctx *)
        let substctx = compose_subst env ~sigma:evd substf lhs' in
        (* Feedback.msg_debug Pp.(str"substituted context: " ++ pr_context_map env evd substctx);  *)
        substctx
    with Not_found (* lookup *) -> lhs') (id_subst ctx) s
  in
  let csubst =
    compose_subst env ~sigma:evd
    (compose_subst env ~sigma:evd subst lhs) cutprob
  in subst, csubst

let subst_protos info s gr =
  let open Context.Rel.Declaration in
  let modified = ref false in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, cst = EConstr.fresh_global env sigma gr in
  let ty = Retyping.get_type_of env sigma cst in
  let rec aux env sigma args ty =
    match kind sigma ty with
    | Constr.Prod (na, b, ty) ->
      begin try match na.binder_name with
        | Name id ->
          let cst = List.find (fun s -> CString.is_prefix (Id.to_string (Label.to_id (Constant.label s))) (Id.to_string id)) s in
          let ctx, concl = decompose_prod_decls sigma b in
          let lctx = List.tl ctx in
          let sigma, cstref = EConstr.fresh_global env sigma (GlobRef.ConstRef cst) in
          let appl = it_mkLambda_or_LetIn (mkApp (cstref, extended_rel_vect 1 lctx)) ctx in
          equations_debug Pp.(fun () -> str"Replacing variable with " ++ Printer.pr_econstr_env env sigma appl);
          modified := true;
          aux env sigma (appl :: args) (subst1 appl ty)
        | Anonymous -> raise Not_found
        with Not_found ->
          let sigma, term = aux (push_rel (LocalAssum (na, b)) env)
              sigma (mkRel 1 :: List.map (lift 1) args) ty in
          sigma, mkLambda (na, b, term) end
    | Constr.LetIn (na, b, t, ty) ->
      let sigma, term = aux (push_rel (LocalDef (na, b, t)) env) sigma (List.map (lift 1) args) ty in
      sigma, mkLetIn (na, b, t, term)
    | _ -> let term = mkApp (cst, CArray.rev_of_list args) in
      sigma, term
  in
  let sigma, term = aux env sigma [] ty in
  if !modified then
    (* let ty = Reductionops.nf_beta env sigma ty in *)
    (equations_debug Pp.(fun () -> str"Fixed hint " ++ Printer.pr_econstr_env env sigma term);
     let id = Nameops.add_suffix (Nametab.basename_of_global gr) "_hint" in
     let cst, (_sigma, _ec) = Equations_common.declare_constant id term None ~poly:info.poly ~kind:(Decls.IsDefinition info.decl_kind) sigma in
     GlobRef.ConstRef cst)
  else gr
  [@@ocaml.warning "-3"]

let wf_hint_warning = CWarnings.create ~name:"wf-obligation-cannot-be-used" ~category:equations_category
  Pp.(fun (gr, msg) -> str"The decreasing recursive call obligation " ++ Printer.pr_global gr ++ str" could not be defined as a hint: " ++ fnl () ++ msg)

let declare_wf_obligations s info =
  let make_resolve gr =
    equations_debug Pp.(fun () -> str"Declaring wf obligation " ++ Printer.pr_global gr);
    (Hints.empty_hint_info, true, subst_protos info s gr)
  in
  let dbname = Principles_proofs.wf_obligations_base info in
  let locality = if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal in
  Hints.create_hint_db false dbname TransparentState.full false;
  List.iter (fun obl ->
      let hint = make_resolve (GlobRef.ConstRef obl) in
      try Hints.add_hints ~locality
            [dbname]
            (Hints.HintsResolveEntry [hint])
      with CErrors.UserError msg (* Cannot be used as a hint *) ->
        wf_hint_warning (GlobRef.ConstRef obl, msg))
    info.comp_obls

let map_fix_subst evd ctxmap s =
  List.map (fun (id, (recarg, f)) -> (id, (recarg, mapping_constr evd ctxmap f))) s

(* Not necessary? If p.id is part of the substitution but isn't in the context we ignore it *)
let _program_fixdecls p fixdecls =
  match p.Syntax.program_rec with
  | Some (Structural NestedNonRec) -> (* Actually the definition is not self-recursive *)
     List.filter (fun decl ->
         let na = Context.Rel.Declaration.get_name decl in
         let id = Nameops.Name.get_id na in
         not (Id.equal id p.program_id)) fixdecls
  | _ -> fixdecls

let push_mapping_context env sigma decl (map, cut) =
  let open Context.Rel.Declaration in
  let decl' = map_rel_declaration (mapping_constr sigma cut) decl in
  let declassum = LocalAssum (get_annot decl, get_type decl) in
  { src_ctx = decl :: map.src_ctx;
    map_inst = PRel 1 :: List.map (lift_pat 1) map.map_inst;
    tgt_ctx = decl' :: map.tgt_ctx },
  lift_subst env sigma cut [declassum]

(** Assumes the declaration already live in \Gamma to produce \Gamma, decls |- ps : \Delta, decls *)
let push_decls_map env evd (ctx : context_map) cut (g : rel_context) =
  let map, _ = List.fold_right (fun decl acc -> push_mapping_context env evd decl acc) g (ctx, cut) in
  check_ctx_map env evd map

let _prsubst env evd s = Pp.(prlist_with_sep spc (fun (id, (recarg, f)) ->
     str (Id.to_string id) ++ str" -> " ++ Printer.pr_econstr_env env !evd f) s)

let subst_rec_programs env evd ps =
  let where_map = ref PathMap.empty in
  let evd = ref evd in
  let cut_problem s ctx' = cut_problem !evd s ctx' in
  let subst_rec cutprob s lhs = subst_rec env !evd cutprob s lhs in
  let rec subst_programs path s ctxlen progs oterms =
    let fixsubst =
      let fn p oterm =
        match p.program_info.program_rec with
        | Some r ->
          let recarg = match r with 
            | Structural _ -> None 
            | WellFounded _ -> Some (Context.Rel.nhyps p.program_info.program_sign - ctxlen) in
          let oterm = lift (List.length p.program_prob.src_ctx - ctxlen) oterm in
          Some (p.program_info.program_id, (recarg, oterm))
        | None -> None
      in
      let fixdecls = List.map2 fn progs oterms in
      List.rev fixdecls
    in
    let fixsubst = CList.map_filter (fun x -> x) fixsubst in
    (* The previous prototypes must be lifted w.r.t. the new variables bound in the where. *)
    let lifts = List.map (fun (id, (recarg, b)) ->
        (id, (recarg, lift (List.length fixsubst) b))) s in
    let s' = fixsubst @ lifts in
    (* Feedback.msg_debug Pp.(str"In subst_programs, pr_substs" ++ prsubst env evd s'); *)
    let one_program p oterm =
      let rec_prob, rec_arity =
        match p.program_rec with
        | Some { rec_prob; rec_arity } -> rec_prob, rec_arity
        | None -> p.program_prob, p.program_info.program_arity
      in
      let prog_info = p.program_info in
      let cutprob_sign = cut_problem s prog_info.program_sign in
      (* Feedback.msg_debug Pp.(str"In subst_programs: " ++ pr_context env !evd prog_info.program_sign);
       * Feedback.msg_debug Pp.(str"In subst_programs: cutprob_sign " ++ pr_context_map env !evd cutprob_sign); *)
      let cutprob_subst, _ = subst_rec cutprob_sign s (id_subst prog_info.program_sign) in
      (* Feedback.msg_debug Pp.(str"In subst_programs: subst_rec failed " ++ pr_context env !evd prog_info.program_sign); *)
      let program_info' =
        { prog_info with
          program_rec = None;
          program_sign = cutprob_subst.src_ctx;
          program_arity = mapping_constr !evd cutprob_subst prog_info.program_arity }
      in
      let program' = { p with program_info = program_info' } in
      let path' = p.program_info.program_id :: path in
      (* Feedback.msg_debug Pp.(str"In subst_programs, cut_problem s'" ++ pr_context env !evd (pi1 rec_prob)); *)
      let rec_cutprob = cut_problem s' rec_prob.src_ctx in
      let splitting' =
          aux rec_cutprob s' program' oterm path' p.program_splitting
      in
      let term', ty' = term_of_tree env evd (ESorts.make prog_info.program_sort) splitting' in
      { program_rec = None;
        program_info = program_info';
        program_prob = id_subst cutprob_sign.tgt_ctx;
        program_term = term';
        program_splitting = splitting' }
    in List.map2 one_program progs oterms

  and aux cutprob s p f path = function
    | Compute (lhs, where, ty, c) ->
      let ctx = lhs.src_ctx in
      let subst, lhs' = subst_rec cutprob s lhs in
      let lhss = map_fix_subst !evd lhs s in
      let progctx = (extend_prob_ctx (where_context where) lhs) in
      let substprog, _ = subst_rec cutprob s progctx in
      let islogical = List.exists (fun (id, (recarg, f)) -> Option.has_some recarg) s in
      let subst_where ({where_program; where_path; where_orig;
                        where_program_args;
                        where_type} as w) (subst_wheres, wheres) =
        (* subst_wheres lives in lhs', i.e. has prototypes substituted already *)
        let wcontext = where_context subst_wheres in
        let cutprob' = cut_problem s subst.tgt_ctx in
        (* Feedback.msg_debug Pp.(str"where_context in subst rec : " ++ pr_context env !evd wcontext);
         * Feedback.msg_debug Pp.(str"lifting subst : " ++ pr_context_map env !evd subst);
         * Feedback.msg_debug Pp.(str"cutprob : " ++ pr_context_map env !evd cutprob'); *)
        let wsubst0 = push_decls_map env !evd subst cutprob' wcontext in
        (* Feedback.msg_debug Pp.(str"new substitution in subst rec : " ++ pr_context_map env !evd wsubst0); *)
        let ctxlen = List.length wcontext + List.length ctx in
        let wp = where_program in
        let where_type = mapping_constr !evd wsubst0 where_type in
        (* The substituted prototypes must be lifted w.r.t. the new variables bound in this where and
           preceding ones. *)
        let s = List.map (fun (id, (recarg, b)) ->
            (id, (recarg, lift ((* List.length subst_wheres + *)
                                List.length wp.program_prob.src_ctx - List.length ctx) b))) lhss in
        let wp' =
          match subst_programs path s ctxlen [wp] [where_term w] with
          | [wp'] -> wp'
          | _ -> assert false
        in
        let wp', args' =
          if islogical || (match wp.program_rec with Some { rec_node = WfRec _ } -> true | _ -> false) then
            let id = Nameops.add_suffix (path_id where_path) "_unfold_eq" in
            let id = Namegen.next_global_ident_away (Global.safe_env ()) id Id.Set.empty in
            let where_program_term = mapping_constr !evd wsubst0 wp.program_term in
            let where_program_args = List.map (mapping_constr !evd wsubst0) where_program_args in
            where_map := PathMap.add where_path
                (applistc where_program_term where_program_args (* substituted *), id, wp'.program_splitting)
                !where_map;
            let where_program_args = extended_rel_list 0 lhs'.src_ctx in
            wp', where_program_args
          else
            let where_program_term = mapping_constr !evd wsubst0 wp.program_term in
            let where_program_args = List.map (mapping_constr !evd wsubst0) where_program_args in
            (* where_map := PathMap.add where_path
             *     (applistc where_program_term where_program_args (\* substituted *\), Id.of_string ""(\*FIXNE*\), wp'.program_splitting)
             *     !where_map; *)
            (* let where_program_args = extended_rel_list 0 (pi1 lhs') in *)
            { wp' with program_term = where_program_term }, where_program_args
        in
        let subst_where =
          {where_program = wp';
           where_program_orig = wp.program_info;
           where_program_args = args';
           where_path;
           where_orig;
           where_context_length = List.length lhs'.src_ctx;
           where_type }
        in (subst_where :: subst_wheres, w :: wheres)
      in
      let where', _ = List.fold_right subst_where where ([], []) in
      let c' = mapping_rhs !evd substprog c in
      let c' = map_rhs (Reductionops.nf_beta env !evd) (fun i -> i) c' in
      Compute (lhs', where', mapping_constr !evd substprog ty, c')

    | Split (lhs, n, ty, cs) ->
      let subst, lhs' = subst_rec cutprob s lhs in
      let n' = destRel !evd (mapping_constr !evd subst (mkRel n)) in
      Split (lhs', n', mapping_constr !evd subst ty,
        Array.map (Option.map (aux cutprob s p f path)) cs)

    | Mapping (lhs, c) ->
      let subst, lhs' = subst_rec cutprob s lhs in
      Mapping (lhs', aux cutprob s p f path c)

    | Refined (lhs, info, sp) ->
      let (id, c, cty), ty, arg, oterm, args, revctx, newprob, newty =
        info.refined_obj, info.refined_rettyp,
        info.refined_arg, info.refined_term, info.refined_args,
        info.refined_revctx, info.refined_newprob, info.refined_newty
      in
      (* Feedback.msg_debug Pp.(str"Before map to newprob " ++ prsubst env evd s); *)
      let lhss = map_fix_subst !evd lhs s in
      (* Feedback.msg_debug Pp.(str"lhs subst " ++ prsubst env evd lhss); *)
      let newprobs = map_fix_subst !evd info.refined_newprob_to_lhs lhss in
      (* Feedback.msg_debug Pp.(str"newprob subst: " ++ prsubst env evd newprobs);
      Feedback.msg_debug Pp.(str"Newprob to lhs: " ++ pr_context_map env !evd info.refined_newprob_to_lhs);
      Feedback.msg_debug Pp.(str"Newprob : " ++ pr_context_map env !evd newprob); *)
      let cutnewprob = cut_problem newprobs newprob.tgt_ctx in
      (* Feedback.msg_debug Pp.(str"cutnewprob : " ++ pr_context_map env !evd cutnewprob); *)
      let subst', newprob' = subst_rec cutnewprob newprobs newprob in
      (* Feedback.msg_debug Pp.(str"subst' : " ++ pr_context_map env !evd subst'); *)
      let subst, lhs' = subst_rec cutprob s lhs in
      (* Feedback.msg_debug Pp.(str"subst = " ++ pr_context_map env !evd subst); *)
      let _, revctx' = subst_rec (cut_problem s revctx.tgt_ctx) lhss revctx in
      let _, newprob_to_prob' =
        subst_rec (cut_problem lhss info.refined_newprob_to_lhs.tgt_ctx) lhss info.refined_newprob_to_lhs in
      let islogical = List.exists (fun (id, (recarg, f)) -> Option.has_some recarg) s in
      let path' = info.refined_path in
      let s' = aux cutnewprob newprobs p f path' sp in
      let count_lets len =
        let open Context.Rel.Declaration in
        let ctx' = newprob'.src_ctx in
        let rec aux ctx len =
          if len = 0 then 0
          else
            match ctx with
            | LocalAssum _ :: ctx -> succ (aux ctx (pred len))
            | LocalDef _ :: ctx -> succ (aux ctx len)
            | [] -> 0
          in aux (List.rev ctx') len
      in
      let refarg = ref (0,0) in
      let refhead =
        if islogical then
          let term', _ = term_of_tree env evd (ESorts.make p.program_info.program_sort) s' in
          term'
         else mapping_constr !evd subst oterm
      in
      let args', filter =
        CList.fold_left_i
          (fun i (acc, filter) c ->
            if i == snd arg then
              (let len = List.length acc in
              refarg := (count_lets len, len));
            if isRel !evd c then
              let d = List.nth lhs.src_ctx (pred (destRel !evd c)) in
              if List.mem_assoc (Nameops.Name.get_id (get_name d)) s then acc, filter
              else mapping_constr !evd subst c :: acc, i :: filter
            else mapping_constr !evd subst c :: acc, i :: filter)
          0 ([], []) args
      in 
      let args' = List.rev_map (Reductionops.nf_beta env !evd) args' in
      equations_debug Pp.(fun () -> str"Chopped args: " ++ prlist_with_sep spc (Printer.pr_econstr_env (push_rel_context subst.src_ctx env) !evd) args');
      let term', args', arg', filter =
        if islogical then
          refhead, args', !refarg, None
        else
          (let sigma, refargs = constrs_of_pats ~inacc_and_hide:false env !evd subst'.map_inst in
           let refterm = it_mkLambda_or_LetIn (applistc refhead (List.rev refargs)) subst'.src_ctx in
           equations_debug Pp.(fun () -> str"refterm: " ++
              (Printer.pr_econstr_env  env !evd refterm));
          let refarg = (fst arg - List.length s, snd arg - List.length s) in
          (refterm, args', refarg, Some (List.rev filter)))
      in
      let c' = Reductionops.nf_beta env !evd (mapping_constr !evd subst c) in
      let info =
        { refined_obj = (id, c', mapping_constr !evd subst cty);
          refined_rettyp = mapping_constr !evd subst ty;
          refined_arg = arg';
          refined_path = path';
          refined_term = term';
          refined_filter = filter;
          refined_args = args';
          refined_revctx = revctx';
          refined_newprob = newprob';
          refined_newprob_to_lhs = newprob_to_prob';
          refined_newty = mapping_constr !evd subst' newty }
      in Refined (lhs', info, s')
  in
  let programs' = subst_programs [] [] 0 ps (List.map (fun p -> p.program_term) ps) in
  !where_map, programs'

let unfold_programs ~pm env evd flags rec_type progs =
  let where_map, progs' = subst_rec_programs env !evd (List.map fst progs) in
  equations_debug (fun () -> Pp.str"subst_rec finished");
  if PathMap.is_empty where_map && not (has_logical rec_type) then
    let one_program (p, prog) p' =
      let norecprob = Context_map.id_subst (program_sign p) in
      let eqninfo =
        Principles_proofs.{ equations_id = p.program_info.program_id;
                            equations_where_map = where_map;
                            equations_f = p.program_term;
                            equations_prob = norecprob }
      in
      let p = { p with program_splitting = p'.program_splitting } in
      p, None, prog, eqninfo
    in pm, List.map2 one_program progs progs'
  else
    let one_program pm (p, prog) unfoldp =
      let pi = p.program_info in
      let i = pi.program_id in
      let sign = pi.program_sign in
      let arity = pi.program_arity in
      let prob = Context_map.id_subst sign in
      (* let () = Feedback.msg_debug (str"defining unfolding" ++ spc () ++ pr_splitting env split) in *)
      (* We first define the unfolding and show the fixpoint equation. *)
      let unfoldi = Nameops.add_suffix i "_unfold" in
      let unfpi =
        { pi with program_id = unfoldi;
                  program_sign = sign;
                  program_arity = arity }
      in
      let unfoldp = make_single_program env evd flags unfpi prob unfoldp.program_splitting None in
      let (unfoldp, term_info), pm, _pstate = define_program_immediate ~pm env evd 
        UState.default_univ_decl [None] [] flags ~unfold:true unfoldp in
      let eqninfo =
        Principles_proofs.{ equations_id = i;
                            equations_where_map = where_map;
                            equations_f = unfoldp.program_term;
                            equations_prob = prob }
      in
      let cst, _ = destConst !evd unfoldp.program_term in
      let cpi' = { program_cst = cst;
                   program_split_info = term_info } in
      pm, (p, Some (unfoldp, cpi'), prog, eqninfo)
    in
    CList.fold_left2_map one_program pm progs progs'

let subst_app sigma f fn c =
  let rec aux n c =
    match kind sigma c with
    | Constr.App (f', args) when eq_constr sigma f f' ->
      let args' = Array.map (map_with_binders sigma succ aux n) args in
      fn n f' args'
    | Constr.Var _ when eq_constr sigma f c ->
       fn n c [||]
    | _ -> map_with_binders sigma succ aux n c
  in aux 0 c

let substitute_alias evd ((f, fargs), term) c =
  subst_app evd f (fun n f args ->
      if n = 0 then
        let args' = filter_arguments fargs (Array.to_list args) in
        applist (term, args')
      else mkApp (f, args)) c

let substitute_aliases evd fsubst c =
  List.fold_right (substitute_alias evd) fsubst c

type alias = ((EConstr.t * int list) * Names.Id.t * Splitting.splitting)

let make_alias (f, id, s) = ((f, []), id, s)

let smash_rel_context sigma ctx =
  let open Context.Rel.Declaration in
  List.fold_right
    (fun decl (subst, pats, ctx') ->
       match get_value decl with
       | Some b ->
         let b' = substl subst b in
         (b' :: subst, List.map (lift_pat 1) pats, ctx')
       | None -> (mkRel 1 :: List.map (lift 1) subst,
                  PRel 1 :: List.map (lift_pat 1) pats,
                  map_constr (Vars.substl subst) decl :: ctx'))
    ctx ([], [], [])

let _remove_let_pats sigma subst patsubst pats =
  let remove_let pat pats =
    match pat with
    | PRel n ->
      let pat = List.nth patsubst (pred n) in
      (match pat with
       | PInac _ -> pats
       | p -> p :: pats)
    | _ -> specialize sigma patsubst pat :: pats
  in
  List.fold_right remove_let pats []

let smash_ctx_map env sigma m =
  let r = m.tgt_ctx in
  let subst, patsubst, r' = smash_rel_context sigma r in
  let smashr' = { src_ctx = r; map_inst = patsubst; tgt_ctx = r' } in
  compose_subst env ~sigma m smashr', subst

let pattern_instance ctxmap =
  List.rev_map pat_constr (filter_def_pats ctxmap)

type computation = Computation of
  Equations_common.rel_context * EConstr.t *
    alias option * EConstr.constr list * EConstr.t *
    EConstr.t * (node_kind * bool) * Splitting.splitting_rhs *
    ((EConstr.t * int list) *
    alias option * Splitting.path * Equations_common.rel_context *
    EConstr.t * EConstr.constr list * (EConstr.constr * (int * int)) option *
    computation list)
    list option

let computations env evd alias refine p eqninfo : computation list =
  let { equations_prob = prob;
        equations_where_map = wheremap;
        equations_f = f } = eqninfo in
  let rec program_computations env prob f alias fsubst refine p : computation list =
    computations env prob f alias fsubst (fst refine, false) p.program_splitting
  and computations env prob f alias fsubst refine = function
  | Compute (lhs, where, ty, c) ->
     let where_comp w (wheres, where_comps) =
       (* Where term is in lhs + wheres *)
       let lhsterm = substl wheres (where_term w) in
       let term, args = decompose_app_list evd lhsterm in
       let alias, fsubst =
         try
           let (f, id, s) = PathMap.find w.where_path wheremap in
           let f, fargs = decompose_appvect evd f in
           let args = match_arguments evd (arguments evd (where_term w)) fargs in
           let fsubst = ((f, args), term) :: fsubst in
           (* Feedback.msg_debug Pp.(str"Substituting " ++ Printer.pr_econstr_env env evd f ++
                                  spc () ++
                                  prlist_with_sep spc int args ++ str" by " ++
                                  Printer.pr_econstr_env env evd term); *)
           Some ((f, args), id, s), fsubst
         with Not_found -> None, fsubst
       in
       let term_ty = Retyping.get_type_of env evd term in
       let subterm, filter =
         let rec aux ty i args' =
           match kind evd ty, args' with
           | Constr.Prod (na, b, ty), a :: args' ->
             if EConstr.isRel evd a then (* A variable from the context that was not substituted
                                  by a recursive prototype, we keep it *)
               let term', len = aux ty (succ i) args' in
               mkLambda (na, b, term'), i :: len
             else
               (* The argument was substituted, we keep that substitution *)
               let term', len = aux (subst1 a ty) (succ i) args' in
               term', len
           | _, [] -> lhsterm, []
           | _, _ :: _ -> assert false
         in aux term_ty 0 args
       in
       let wsmash, smashsubst = smash_ctx_map env evd (id_subst w.where_program.program_info.program_sign) in
       let comps =
         program_computations env wsmash subterm None fsubst (Regular,false) w.where_program
       in
       let arity = w.where_program.program_info.program_arity in
       let termf =
         if not (PathMap.is_empty wheremap) then
           subterm, [0]
         else
           subterm, filter
       in
       let where_comp =
         (termf, alias, w.where_orig, wsmash.src_ctx, (* substl smashsubst *) arity,
          pattern_instance wsmash, None (* no refinement *), comps)
       in (lhsterm :: wheres, where_comp :: where_comps)
     in
     let inst, wheres = List.fold_right where_comp where ([],[]) in
     let ctx = compose_subst env ~sigma:evd lhs prob in
     if !Equations_common.debug then
       Feedback.msg_debug Pp.(str"where_instance: " ++ prlist_with_sep spc (Printer.pr_econstr_env env evd) inst);
     let envlhs = (push_rel_context lhs.src_ctx env) in 
     let envwhere = push_rel_context (where_context where) envlhs in
     let fn c =
      (* Feedback.msg_debug Pp.(str"substituting in c= " ++ Printer.pr_econstr_env envwhere evd c); *)
       let c' = Reductionops.nf_beta env evd (substl inst c) in
       (* Feedback.msg_debug Pp.(str"after where instance substitution: " ++ Printer.pr_econstr_env envlhs evd c'); *)
       substitute_aliases evd fsubst c'
     in
     let c' = map_rhs (fun c -> fn c) (fun x -> x) c in
     if !Equations_common.debug then
      (Feedback.msg_debug Pp.(str"substituting in: " ++ pr_splitting_rhs ~verbose:true envlhs envwhere evd lhs c ty);
      Feedback.msg_debug Pp.(str"substituted: " ++ pr_splitting_rhs ~verbose:true envlhs envlhs evd lhs c' ty));
     let patsconstrs = pattern_instance ctx in
     let ty = substl inst ty in
     [Computation (ctx.src_ctx, f, alias, patsconstrs, ty,
      f, (Where, snd refine), c', Some wheres)]

  | Split (_, _, _, cs) ->
    Array.fold_left (fun acc c ->
        match c with
   | None -> acc
   | Some c ->
   acc @ computations env prob f alias fsubst refine c) [] cs

  | Mapping (lhs, c) ->
     let _newprob = compose_subst env ~sigma:evd prob lhs in
     computations env prob f alias fsubst refine c

  | Refined (lhs, info, cs) ->
     let (id, c, t) = info.refined_obj in
     let s = compose_subst env ~sigma:evd lhs prob in
     let patsconstrs = pattern_instance s in
     let refineds = compose_subst env ~sigma:evd info.refined_newprob_to_lhs s in
     let refinedpats = pattern_instance refineds in
     let progterm = applistc info.refined_term info.refined_args in
     let filter = Option.default [Array.length (arguments evd info.refined_term)] info.refined_filter in
     (* Feedback.msg_debug Pp.(str"At refine node: " ++ pr_context_map env evd info.refined_newprob);
     Feedback.msg_debug Pp.(str"At refine node: " ++ pr_context_map env evd info.refined_revctx);
     Feedback.msg_debug Pp.(str"At refine node, refined term: " ++ Printer.pr_econstr_env 
      (push_rel_context (pi1 lhs) env) evd info.refined_term);
     Feedback.msg_debug Pp.(str"At refine node, program term: " ++ Printer.pr_econstr_env 
      (push_rel_context (pi1 lhs) env) evd progterm); *)
     [Computation (lhs.src_ctx, f, alias, patsconstrs, info.refined_rettyp, f, (Refine, true),
      RProgram progterm,
      Some [(info.refined_term, filter), None, info.refined_path, info.refined_newprob.src_ctx,
            info.refined_newty, refinedpats,
            Some (mapping_constr evd info.refined_newprob_to_lhs c, info.refined_arg),
            computations env info.refined_newprob (lift 1 info.refined_term) None fsubst (Regular, true) cs])]

  in program_computations env prob f alias [] refine p

let constr_of_global_univ gr u =
  let open Names.GlobRef in
  match gr with
  | ConstRef c -> mkConstU (c, u)
  | IndRef i -> mkIndU (i, u)
  | ConstructRef c -> mkConstructU (c, u)
  | VarRef id -> mkVar id

let declare_funelim ~pm info env evd is_rec protos progs
                    ind_stmts all_stmts sign app subst inds kn comb
                    sort indgr ectx =
  let id = Id.of_string info.base_id in
  let leninds = List.length inds in
  let elim = comb in
  let elimc, elimty =
    let elimty, uctx = Typeops.type_of_global_in_context (Global.env ()) elim in
    let () = evd := Evd.from_env (Global.env ()) in
    if is_polymorphic info then
      (* We merge the contexts of the term and eliminator in which
         ind_stmts and all_stmts are derived, universe unification will
         take care of unifying the eliminator's fresh instance with the
         universes of the constant and the functional induction lemma. *)
      let () = evd := Evd.merge_ustate !evd info.term_ustate in
      let () = evd := Evd.merge_ustate !evd ectx in
      let sigma, elimc = Evd.fresh_global (Global.env ()) !evd elim in
      let elimty = Retyping.get_type_of env sigma elimc in
      let () = evd := sigma in
      elimc, elimty
    else (* If not polymorphic, we just use the global environment's universes for f and elim *)
      (let elimc = constr_of_global_univ elim EInstance.empty in
       elimc, of_constr elimty)
  in
  let nargs, newty =
    compute_elim_type env evd info.user_obls is_rec protos kn leninds ind_stmts all_stmts
                      sign app elimty
  in
  let hookelim { Declare.Hook.S.dref; _ } =
    let env = Global.env () in
    let evd = Evd.from_env env in
    let f_gr = Nametab.locate (Libnames.qualid_of_ident id) in
    let evd, f = new_global evd f_gr in
    let evd, elimcgr = new_global evd dref in
    let evd, cl = functional_elimination_class evd in
    let evd, args_of_elim = coq_nat_of_int evd nargs in
    let args = [Retyping.get_type_of env evd f; f;
                Retyping.get_type_of env evd elimcgr;
                args_of_elim; elimcgr]
    in
    let instid = Nameops.add_prefix "FunctionalElimination_" id in
    let poly = info.poly in
    ignore(Equations_common.declare_instance instid ~poly evd [] cl args)
  in
  let tactic = ind_elim_tac elimc leninds (List.length progs) info indgr in
  let _ =
    try
      equations_debug Pp.(fun () -> str"Type-checking elimination principle: " ++ fnl () ++
                                    Printer.pr_econstr_env env !evd newty);
      ignore (e_type_of (Global.env ()) evd newty);
      equations_debug (fun () -> Pp.str"Functional elimination principle type-checked");
    with Type_errors.TypeError (env, tyerr) ->
      CErrors.user_err Pp.(str"Error while typechecking elimination principle type: " ++
                           Himsg.explain_pretype_error env !evd
                             (Pretype_errors.TypingError (Pretype_errors.of_type_error tyerr)))
  in
  let newty = collapse_term_qualities (Evd.ustate !evd) (EConstr.to_constr !evd newty) in 
  let cinfo = Declare.CInfo.make ~name:(Nameops.add_suffix id "_elim") ~typ:newty () in
  let info = Declare.Info.make ~poly:info.poly ~scope:info.scope ~hook:(Declare.Hook.make hookelim) ~kind:(Decls.IsDefinition info.decl_kind) () in
  let pm = Declare.Obls.add_definition ~pm ~cinfo ~info ~tactic ~opaque:false
      ~uctx:(Evd.ustate !evd) [||] in
  pm

let mkConj evd sort x y =
  let prod = get_efresh logic_product evd in
    mkApp (prod, [| x; y |])

let functional_proof_warning = 
  CWarnings.create ~name:"functional-induction-derivation-failure" ~category:equations_category
    Pp.(fun msg -> str"Functional induction/elimination principle could not be proved automatically: " ++ msg)

let declare_funind ~pm info alias env evd is_rec protos progs
                   ind_stmts all_stmts sign inds kn comb sort f split =
  let poly = info.term_info.poly in
  let id = Id.of_string info.term_info.base_id in
  let indid = Nameops.add_suffix id "_graph_correct" in
  (* Record nested statements which can be repeated during the proof *)
  let nested_statements = ref [] in
  let statement =
    let stmt (i, ((f,_), alias, path, sign, ar, _, _, (nodek, cut)), _) =
      if not (regular_or_nested nodek) then None else
      let f, split, unfsplit =
        match alias with
        | Some ((f,_), _, recsplit) -> f, recsplit, Some split
        | None -> f, split, None
      in
      let args = extended_rel_list 0 sign in
      let app = applist (f, args) in
      let ind = Nameops.add_suffix (path_id path)(* Id.of_string info.term_info.base_id) *)
                                   ("_graph" (* ^ if i == 0 then "" else "_" ^ string_of_int i *)) in
      let indt = e_new_global evd (global_reference ind) in
      let ty = it_mkProd_or_subst env !evd (applist (indt, args @ [app])) sign in
      let (prog, _, _, _) = List.find (fun (p, _, _, _) -> Id.equal p.program_info.program_id (path_id path)) progs in
      if nested nodek then nested_statements := (path_id path, ty, prog) :: !nested_statements;
      Some ty
    in
    match ind_stmts with
    | [] -> assert false
    | [hd] -> Option.get (stmt hd)
    | hd :: tl ->
       let l, last =
         let rec aux l =
           let last, l = CList.sep_last l in
           match stmt last with
           | None -> aux l
           | Some t -> t, l
         in aux ind_stmts
       in
       List.fold_right (fun x acc -> match stmt x with
                                     | Some t -> mkConj evd sort t acc
                                     | None -> acc) last l
  in
  let args = Termops.rel_list 0 (List.length sign) in
  let f =
    match alias with
    | Some ((f, _), _, _) -> f
    | None -> f
  in
  let app = applist (f, args) in
  let hookind { Declare.Hook.S.uctx; scope; dref; _ } pm =
    let env = Global.env () in (* refresh *)
    let locality = if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal in
    Hints.add_hints ~locality [info.term_info.base_id]
                    (Hints.HintsImmediateEntry [dref]);
    let pm =
      try declare_funelim ~pm info.term_info env evd is_rec protos progs
            ind_stmts all_stmts sign app scope inds kn comb sort dref uctx
      with
      | Type_errors.TypeError (env, tyerr) ->
        CErrors.user_err Pp.(str"Functional elimination principle could not be proved automatically: " ++
                             Himsg.explain_pretype_error env !evd
                               (Pretype_errors.TypingError (Pretype_errors.of_type_error tyerr)))
      | Pretype_errors.PretypeError (env, sigma, tyerr) ->
        CErrors.user_err Pp.(str"Functional elimination principle could not be proved automatically: " ++
                             Himsg.explain_pretype_error env sigma tyerr)
      | e ->
        functional_proof_warning Pp.(fnl () ++ CErrors.print e);
        pm
    in
    let evd = Evd.from_env env in
    let f_gr = Nametab.locate (Libnames.qualid_of_ident id) in
    let evd, f = new_global evd f_gr in
    let evd, indcgr = new_global evd dref in
    let evd, cl = functional_induction_class evd in
    let args = [Retyping.get_type_of env evd f; f;
                Retyping.get_type_of env evd indcgr; indcgr]
    in
    let instid = Nameops.add_prefix "FunctionalInduction_" id in
    ignore(Equations_common.declare_instance instid ~poly evd [] cl args);
    (* If desired the definitions should be made transparent again. *)
    begin
    if !Equations_common.equations_transparent then
      (Global.set_strategy (Conv_oracle.EvalConstRef (fst (destConst evd f))) Conv_oracle.transparent;
       match alias with
       | None -> ()
       | Some ((f, _), _, _) -> Global.set_strategy (Conv_oracle.EvalConstRef (fst (destConst evd f))) Conv_oracle.transparent)
    else
      ((* Otherwise we turn them opaque and let that information be discharged as well *)
        Lib.add_leaf (inOpacity (fst (destConst evd f)));
        match alias with
        | None -> ()
        | Some ((f, _), _, _) -> Lib.add_leaf (inOpacity (fst (destConst evd f))))
    end;
    pm
  in
  let evm, stmtt = Typing.type_of (Global.env ()) !evd statement in
  let () = evd := evm in
  let to_constr c = collapse_term_qualities (Evd.ustate !evd) (EConstr.to_constr !evd c) in
  let stmt = to_constr statement and f = to_constr f in
  let uctx = Evd.ustate (if PolyFlags.univ_poly poly then !evd else Evd.from_env (Global.env ())) in
  let launch_ind ~pm tactic =
    let pm =
      let cinfo = Declare.CInfo.make ~name:indid ~typ:stmt () in
      let info = Declare.Info.make ~poly
          ~kind:(Decls.IsDefinition info.term_info.decl_kind)
          () in
      let obl_hook = Declare.Hook.make_g hookind in
      Declare.Obls.add_definition ~pm ~cinfo ~info ~obl_hook ~opaque:false
        ~tactic:(Tacticals.tclTRY tactic) ~uctx [||]
    in
    let pm = Declare.OblState.view pm in
    if Id.Map.mem indid pm then
      functional_proof_warning Pp.(str "it is left as an obligation.")
  in
  let tac = (ind_fun_tac is_rec f info id !nested_statements progs) in
  try launch_ind ~pm tac
  with Type_errors.TypeError (env, tyerr) ->
    CErrors.user_err Pp.(str"Functional induction principle could not be proved automatically: " ++
                         Himsg.explain_pretype_error env !evd
                           (Pretype_errors.TypingError (Pretype_errors.of_type_error tyerr)))
    | e when CErrors.noncritical e ->
       functional_proof_warning Pp.(fnl () ++ CErrors.print e);
       launch_ind ~pm (Proofview.tclUNIT ())

let max_sort s1 s2 =
  let open Sorts in
  match s1, s2 with
  | (SProp, SProp) | (Prop, Prop) | (Set, Set) -> s1
  | (SProp, (Prop | Set | Type _ as s)) | ((Prop | Set | Type _) as s, SProp) -> s
  | (Prop, (Set | Type _ as s)) | ((Set | Type _) as s, Prop) -> s
  | (Set, Type u) | (Type u, Set) -> Sorts.sort_of_univ (Univ.Universe.sup Univ.Universe.type0 u)
  | (Type u, Type v) -> Sorts.sort_of_univ (Univ.Universe.sup u v)
  | (GSort _, _) | (_, GSort _) -> assert false
  | (VSort _, _) | (_, VSort _) -> assert false

let level_of_context env evd ctx acc =
  let _, lev =
    List.fold_right (fun decl (env, lev) ->
        let s = Retyping.get_sort_of env evd (get_type decl) in
        let s = ESorts.kind evd s in
        (push_rel decl env, max_sort s lev))
                    ctx (env,acc)
  in lev

let all_computations env evd alias progs =
  let comps =
    let fn p unfp =
      let p = Option.default p unfp in
      computations env evd alias (kind_of_prog p.program_info,false) p in
    List.map (fun (p, unfp, prog, eqninfo) -> p, eqninfo, fn p unfp eqninfo) progs
  in
  let rec flatten_comp (Computation (ctx, fl, flalias, pats, ty, f, refine, c, rest)) =
    let rest = match rest with
      | None -> []
      | Some l ->
         CList.map_append (fun (f, alias, path, ctx, ty, pats, newargs, rest) ->
          let nextlevel, rest = flatten_comps rest in
            ((f, alias, path, ctx, ty, pats, newargs, refine), nextlevel) :: rest) l
    in (ctx, fl, flalias, pats, ty, f, refine, c), rest
  and flatten_comps r =
    List.fold_right (fun cmp (acc, rest) ->
      let stmt, rest' = flatten_comp cmp in
        (stmt :: acc, rest' @ rest)) r ([], [])
  in
  let flatten_top_comps (p, eqninfo, one_comps) acc =
    let (top, rest) = flatten_comps one_comps in
    let pi = p.program_info in
    let topcomp = (((eqninfo.equations_f,[]), alias, [pi.program_id],
                    pi.program_sign, pi.program_arity,
                    List.rev_map pat_constr eqninfo.equations_prob.map_inst, None,
                    (kind_of_prog pi,false)), top) in
    topcomp :: (rest @ acc)
  in
  List.fold_right flatten_top_comps comps []

let unfold_fix =
  let open Proofview in
  Proofview.Goal.enter (fun gl ->
      let sigma = Goal.sigma gl in
      match kind sigma (Goal.concl gl) with
      | Constr.App (eq, [| _; lhs; _ |]) ->
        (match kind sigma lhs with
         | Constr.App (fn, args) ->
           (match kind sigma fn with
            | Constr.Fix ((indexes, p), decls) ->
              let fixarg = args.(indexes.(p)) in
              (match kind sigma fixarg with
               | Constr.Var id -> depelim_tac id
               | _ -> tclUNIT ())
            | _ -> tclUNIT ())
         | _ -> tclUNIT ())
      | _ -> tclUNIT ())

let build_equations ~pm with_ind env evd ?(alias:alias option) rec_info progs =
  let () =
    if !Equations_common.debug then
      let open Pp in
      let msg = Feedback.msg_debug in
      msg (str"Definining principles of: " ++
           prlist_with_sep fnl
             (fun (p, unfp, prog, eqninfo) ->
                pr_splitting ~verbose:true env evd p.program_splitting ++ fnl () ++
                (match unfp with
                 | Some unf -> str "and " ++ pr_splitting env evd unf.program_splitting
                 | None -> mt ()))
             progs)
  in
  let env = Global.env () in
  let p, unfp, prog, eqninfo = List.hd progs in
  let user_obls =
    List.fold_left (fun acc (p, unfp, prog, eqninfo) ->
      Id.Set.union prog.program_split_info.user_obls acc) Id.Set.empty progs
  in
  let { equations_id = id;
        equations_where_map = wheremap;
        equations_f = f } = eqninfo in
  let info = prog.program_split_info in
  let sign = program_sign p in
  let cst = prog.program_cst in
  let ocst, _ = destConst evd p.program_term in
  let comps = all_computations env evd alias progs in
  let protos = List.map fst comps in
  let lenprotos = List.length protos in
  let subst_obls =
    CList.map_filter (fun ((f',filter), alias, _, sign, _, _, _, _) ->
        match alias with
        | Some ((f, filter'), id, _) ->
          equations_debug Pp.(fun () -> str"Prototype " ++ Printer.pr_econstr_env env evd f' ++
                                        str"alias: " ++  Printer.pr_econstr_env env evd f);
          Some (fst (destConst evd (fst (decompose_app evd f))))
        | None ->
          equations_debug Pp.(fun () -> str"Prototype " ++ Printer.pr_econstr_env env evd f' ++
                                        str" no alias ");
          None)
      protos
  in
  let () = List.iter (fun (_, _, prog, _) ->
      declare_wf_obligations subst_obls prog.program_split_info) progs
  in
  let protos =
    CList.map_i (fun i ((f',filterf'), alias, path, sign, arity, pats, args, (refine, cut)) ->
      let f' = Termops.strip_outer_cast evd f' in
      let f'hd =
        let ctx, t = decompose_lambda_decls evd f' in
        fst (decompose_app evd t)
      in
      let alias =
        match alias with
        | None -> None
        | Some (f, _, _) -> Some f
      in
      (f'hd, (f',filterf'), alias, lenprotos - i, sign, to_constr evd arity))
      1 protos
  in
  let evd = ref evd in
  let poly = info.poly in
  let statement i filter (ctx, fl, flalias, pats, ty, f', (refine, cut), c) =
    let hd, unf = match flalias with
      | Some ((f', _), unf, _) ->
        let tac = Proofview.tclBIND
            (Tacticals.pf_constr_of_global (Nametab.locate (Libnames.qualid_of_ident unf)))
            Equality.rewriteLR in
        f', tac

      | None -> fl,
        if eq_constr !evd fl f then
          Tacticals.tclORELSE Tactics.reflexivity
            (Tacticals.tclTHEN (unfold_constr !evd f) unfold_fix)
        else Tacticals.tclIDTAC
    in
    let comp = applistc hd pats in
    let body =
      let nf_beta = Reductionops.nf_beta (push_rel_context ctx env) !evd in
      let b = match c with
        | RProgram c ->
            mkEq env evd ty (nf_beta comp) (nf_beta c)
        | REmpty (i, _) ->
           mkApp (coq_ImpossibleCall evd, [| ty; nf_beta comp |])
      in
      let body = it_mkProd_or_LetIn b ctx in
      if !Equations_common.debug then
        Feedback.msg_debug Pp.(str"Typing equation " ++ Printer.pr_econstr_env env !evd body);
      let _ = Equations_common.evd_comb1 (Typing.type_of env) evd body in
      body
    in
    let cstr =
      match c with
      | RProgram c ->
          let len = List.length ctx in
          let hyps, hypslen, c' =
            abstract_rec_calls !evd user_obls rec_info len protos (Reductionops.nf_beta env !evd c)
          in
          let head =
            let f = mkRel (len + (lenprotos - i) + hypslen) in
            if cut then f
            else
              let fn, args = decompose_app_list !evd (Termops.strip_outer_cast !evd fl) in
              applistc f (filter_arguments filter (lift_constrs hypslen args))
          in
          let ty =
            it_mkProd_or_clear !evd
              (it_mkProd_or_clean env !evd
                 (applistc head (lift_constrs hypslen pats @ [c']))
                 hyps) ctx
          in
          if !Equations_common.debug then
            Feedback.msg_debug Pp.(str"Typing constructor " ++ Printer.pr_econstr_env env !evd ty);

          Some ty
      | REmpty (i, _) -> None
    in (refine, unf, body, cstr)
  in
  let statements i ((f', alias, path, sign, arity, pats, args, refine as fs), c) =
    let fs, filter =
      match alias with
      | Some (f', unf, split) ->
         (f', None, path, sign, arity, pats, args, refine), snd f'
      | None -> fs, snd f'
    in fs, List.map (statement i filter) c in
  let stmts = CList.map_i statements 0 comps in
  let ind_stmts = CList.map_i
    (fun i (f, c) -> i, f, CList.map_i (fun j x -> j, x) 1 c) 0 stmts
  in
  let all_stmts = List.concat (List.map (fun (f, c) -> c) stmts) in
  let fnind_map = ref PathMap.empty in
  let declare_one_ind (inds, univs, sorts) (i, (f, alias, path, sign, arity, pats, refs, refine), stmts) =
    let indid = Nameops.add_suffix (path_id path) "_graph" (* (if i == 0 then "_ind" else ("_ind_" ^ string_of_int i)) *) in
    let indapp = List.rev_map (fun x -> Constr.mkVar (Nameops.Name.get_id (get_name x))) sign in
    let () = fnind_map := PathMap.add path (indid,indapp) !fnind_map in
    let constructors = CList.map_filter (fun (_, (_, _, _, n)) -> Option.map (to_constr !evd) n) stmts in
    let consnames = CList.map_filter (fun (i, (r, _, _, n)) ->
      Option.map (fun _ ->
        let suff = (if r != Refine then "_equation_" else "_refinement_") ^ string_of_int i in
          Nameops.add_suffix indid suff) n) stmts
    in
    let merge_universes_of_constr c =
      Univ.Level.Set.union (snd (EConstr.universes_of_constr !evd c)) in
    let univs = Univ.Level.Set.union (snd (universes_of_constr !evd arity)) univs in
    let univs = Context.Rel.(fold_outside (Declaration.fold_constr merge_universes_of_constr) sign ~init:univs) in
    let univs =
      List.fold_left (fun univs c -> Univ.Level.Set.union (snd (universes_of_constr !evd (EConstr.of_constr c))) univs)
        univs constructors in
    let ind_sort =
      let open UnivGen.QualityOrSet in
      match Retyping.get_sort_quality_of env !evd (it_mkProd_or_LetIn arity sign) with
      | QConstant QProp ->
        (* If the program is producing a proof, then we cannot hope to have its
           graph in Type in general (it might be case-splitting on non-strict propositions). *)
        Sorts.prop
      | _ ->
        let ctx = (of_tuple (anonR, None, arity) :: sign) in
        let signlev = level_of_context env !evd ctx sorts in
        signlev
    in
    let entry =
      Entries.{ mind_entry_typename = indid;
                mind_entry_arity = to_constr !evd (it_mkProd_or_LetIn (mkProd (anonR, arity,
                                                                               mkSort (ESorts.make ind_sort))) sign);
                mind_entry_consnames = consnames;
                mind_entry_lc = constructors;
              }
    in ((entry, sign, arity) :: inds, univs, max_sort ind_sort sorts)
  in
  let declare_ind () =
    let inds, univs, sort = List.fold_left declare_one_ind ([], Univ.Level.Set.empty, Sorts.prop) ind_stmts in
    let sigma = Evd.restrict_universe_context !evd univs in
    let sigma = Evd.minimize_universes sigma in
    (* FIXME: try to implement a sane handling of universe state threading *)
    let to_constr sigma c =
      collapse_term_qualities (Evd.ustate sigma) (EConstr.to_constr sigma c)
    in
    let inds =
      List.rev_map (fun (entry, sign, arity) ->
          Entries.{ entry with
                    mind_entry_lc = List.map (to_constr sigma) (List.map of_constr entry.mind_entry_lc);
                    mind_entry_arity =
                      to_constr sigma (it_mkProd_or_LetIn (mkProd (anonR, arity,
                                                                  mkSort (ESorts.make sort))) sign) })
        inds
    in
    let univs, ubinders = Evd.univ_entry ~poly sigma in
    let uctx = match univs with
    | UState.Monomorphic_entry ctx ->
      let () = Global.push_context_set ctx in
      Entries.Monomorphic_ind_entry
    | UState.Polymorphic_entry uctx -> Entries.Polymorphic_ind_entry uctx
    in
    let inductive =
      Entries.{ mind_entry_record = None;
                mind_entry_universes = uctx;
                mind_entry_private = None;
                mind_entry_finite = Declarations.Finite;
                mind_entry_params = []; (* (identifier * local_entry) list; *)
                mind_entry_inds = inds;
                mind_entry_variance = None;
              }
    in
    let () = Goptions.set_bool_option_value_gen ~locality:Goptions.OptLocal ["Elimination";"Schemes"] false in
    let kn = DeclareInd.declare_mutual_inductive_with_eliminations inductive (univs, ubinders) [] in
    let () = Goptions.set_bool_option_value_gen ~locality:Goptions.OptLocal ["Elimination";"Schemes"] true in
    let sort = Inductiveops.top_allowed_sort (Global.env()) (kn,0) in
    let sort_suff = Elimschemes.elimination_suffix sort in
    let kn, comb =
      match inds with
      | [ind] ->
        let scheme = Nameops.add_suffix ind.Entries.mind_entry_typename sort_suff in
        let mutual =
          (CList.map_i (fun i ind ->
               let id = CAst.make @@ scheme in
               (id, false, (kn, i), sort)) 0 inds)
        in
        Indschemes.do_mutual_induction_scheme ~register:true (Global.env()) ~force_mutual:true mutual;
        kn, Smartlocate.global_with_alias (Libnames.qualid_of_ident scheme)
      | _ ->
        let mutual =
          (CList.map_i (fun i ind ->
               let suff = "_mut" in
               let id = CAst.make @@ Nameops.add_suffix ind.Entries.mind_entry_typename suff in
               (id, false, (kn, i), sort)) 0 inds)
        in
        Indschemes.do_mutual_induction_scheme ~register:true (Global.env()) ~force_mutual:true mutual;
        let scheme = Nameops.add_suffix (Id.of_string info.base_id) ("_graph" ^ sort_suff) in
        let mutual = List.map2 (fun (i, _, _, _) (_, (_, _, _, _, _, _, _, (kind, cut)), _) ->
                         i, regular_or_nested_rec kind) mutual ind_stmts in
        let () =
          Indschemes.do_combined_scheme CAst.(make scheme)
            (CList.map_filter (fun ({CAst.loc;v=id}, b) ->
                 if b
                 then Some (Nametab.locate_constant (Libnames.qualid_of_ident ?loc id))
                 else None)
                mutual)
        in kn, Smartlocate.global_with_alias (Libnames.qualid_of_ident scheme)
    in
    let locality = if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal in
    let () =
      List.iteri (fun i ind ->
        let constrs =
          CList.map_i (fun j _ -> Hints.empty_hint_info, true,
            GlobRef.ConstructRef ((kn,i),j)) 1 ind.Entries.mind_entry_lc in
          Hints.add_hints ~locality [info.base_id] (Hints.HintsResolveEntry constrs))
        inds
    in
    let info = { term_info = info; pathmap = !fnind_map; wheremap } in
    declare_funind ~pm info alias (Global.env ()) evd rec_info protos progs
                   ind_stmts all_stmts sign inds kn comb sort
                   f p.program_splitting
  in
  let () = evd := Evd.minimize_universes !evd in
  let () =
    if not (PolyFlags.univ_poly poly) then
      (* Declare the universe context necessary to typecheck the following
          definitions once and for all. *)
      let uctx = Evd.sort_context_set !evd in
      let (_qs, us), (_qcst, ucst) = uctx in
      let () = Global.push_context_set (us, ucst) in
      evd := Evd.from_env (Global.env ())
    else ()
  in
  let eqns = CArray.map_of_list (fun (_, _, stmts) -> Array.make (List.length stmts) false) ind_stmts in
  let proof pm (j, (_, alias, path, sign, arity, pats, refs, refine), stmts) =
    let id = path_id path in
    let proof (pm : Declare.OblState.t) (i, (r, unf, c, n)) =
      let ideq = Nameops.add_suffix id ("_equation_" ^ string_of_int i) in
      let hook { Declare.Hook.S.dref; _ } pm =
        if n != None then add_rew_rule ~l2r:true ~base:info.base_id dref
        else (Classes.declare_instance (Global.env()) !evd None Hints.Local dref
              (* Hints.add_hints ~local:false [info.base_id]  *)
              (*                 (Hints.HintsExternEntry *)
              (*                  (Vernacexpr.{hint_priority = Some 0; hint_pattern = None}, *)
              (*                   impossible_call_tac (GlobRef.ConstRef cst))) *));
        eqns.(j).(pred i) <- true;
        if CArray.for_all (CArray.for_all (fun x -> x)) eqns then (
          let locality = if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal in
          (* From now on, we don't need the reduction behavior of the constant anymore *)
          Hints.(add_hints ~locality [info.base_id]
            (HintsTransparencyEntry (HintsReferences [Evaluable.EvalConstRef ocst], false)));
          Classes.set_typeclass_transparency ~locality [Evaluable.EvalConstRef cst] false;
          (match alias with
           | Some ((f, _), _, _) ->
              let cst' = fst (destConst !evd f) in
              Hints.(add_hints ~locality [info.base_id]
                (HintsTransparencyEntry (HintsReferences [Evaluable.EvalConstRef cst'], false)));
              Global.set_strategy (Conv_oracle.EvalConstRef cst') Conv_oracle.Opaque
           | None -> ());
          Global.set_strategy (Conv_oracle.EvalConstRef cst) Conv_oracle.Opaque;
          if with_ind then (declare_ind (); pm) else pm)
        else pm
      in
      let tac =
        let open Tacticals in
        tclTHENLIST
          [Tactics.intros;
           unf;
           (solve_equation_tac (GlobRef.ConstRef cst));
           (if PathMap.is_empty wheremap then Tacticals.tclIDTAC
            else tclTRY (autorewrites (info.base_id ^ "_where")));
           Tactics.reflexivity]
      in
      let () =
        (* Refresh at each equation, accumulating known constraints. *)
        if not (PolyFlags.univ_poly poly) then evd := Evd.from_env (Global.env ())
        else ()
      in
      (* FIXME: try to implement a sane handling of universe state threading *)
      let c = collapse_term_qualities (Evd.ustate !evd) (to_constr !evd c) in
      let cinfo = Declare.CInfo.make ~name:ideq ~typ:c () in
      let info = Declare.Info.make ~kind:(Decls.IsDefinition info.decl_kind) ~poly () in
      let obl_hook = Declare.Hook.make_g hook in
      let pm = Declare.Obls.add_definition ~pm ~cinfo ~info ~obl_hook ~opaque:false
               ~tactic:tac ~uctx:(Evd.ustate !evd) [||] in
      pm
    in List.fold_left proof pm stmts
  in List.fold_left proof pm ind_stmts
