(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Printer
open Ppconstr
open Util
open Names
open Constr
open Pp
open Glob_term
open List
open Libnames
open Constrexpr_ops
open Constrexpr
open Evar_kinds
open Constrintern

(* Unfortunate copy-paste from Equations_common due to a dependency cycle *)
let pp cmds = Feedback.msg_info cmds
let user_err_loc (loc, pp) = CErrors.user_err ?loc pp
let anomaly ?label pp = CErrors.anomaly ?label pp
let find_global s = lazy (Rocqlib.lib_ref ("equations." ^ s))
let coq_bang = find_global "internal.bang"
let coq_inacc = find_global "internal.inaccessible_pattern"
(* / End of copy-paste *)

type 'a with_loc = Loc.t option * 'a
type identifier = Names.Id.t
   
type provenance = 
  | User
  | Generated
  | Implicit

(** User-level patterns *)
type user_pat =
    PUVar of identifier * provenance
  | PUCstr of constructor * int * user_pats
  | PUInac of Glob_term.glob_constr
  | PUEmpty
and user_pat_loc = (user_pat, [ `any ]) DAst.t
and user_pats = user_pat_loc list

(** AST *)

type pat_expr =
  | PEApp of qualid Constrexpr.or_by_notation with_loc * pat_expr with_loc list
  | PEWildcard
  | PEInac of constr_expr

type user_pat_expr = pat_expr with_loc

type 'a input_pats =
  | SignPats of 'a
  | RefinePats of 'a list

type rec_annotation =
  | Nested
  | Mutual

type user_rec_annot = rec_annotation option

type rec_arg = int * Id.t with_loc option
    
type rec_annot =
  | MutualOn of rec_arg option
  | NestedOn of rec_arg option
  | NestedNonRec

type program_body =
  | ConstrExpr of Constrexpr.constr_expr
  | GlobConstr of Glob_term.glob_constr
  | Constr of EConstr.constr (* We interpret a constr by substituting
                                [Var names] of the lhs bound variables
                                with the proper de Bruijn indices *)

type lhs = user_pats

and ('a,'b) rhs_aux =
    Program of program_body * 'a wheres
  | Empty of identifier with_loc
  | Refine of Constrexpr.constr_expr list * 'b list

and ('a,'b) rhs = ('a, 'b) rhs_aux option (* Empty patterns allow empty r.h.s. *)

and pre_prototype =
  identifier with_loc * Constrexpr.universe_decl_expr option * user_rec_annot *
  Constrexpr.local_binder_expr list * Constrexpr.constr_expr option *
  (Id.t with_loc option, Constrexpr.constr_expr * Constrexpr.constr_expr option) by_annot option

and ('a, 'b) by_annot =
  | Structural of 'a
  | WellFounded of 'b

and 'a where_clause = pre_prototype * 'a list
and 'a wheres = 'a where_clause list * Vernacexpr.notation_declaration list

type program = (signature * clause list) list
and signature = identifier * EConstr.rel_context * constr (* f : Π Δ. τ *)
and clause = Clause of Loc.t option * lhs * (clause, clause) rhs (* lhs rhs *)

type pre_equation = Pre_equation of Constrexpr.constr_expr input_pats * (pre_equation, pre_equation) rhs

type pre_clause = Pre_clause of Loc.t option * lhs * (pre_equation, pre_clause) rhs

type pre_equations = pre_equation where_clause list

let pr_provenance ~with_gen id = function
  | User -> id
  | Generated -> str"_" ++ (if with_gen then id else mt ())
  | Implicit -> str"{" ++ id ++ str"}"

let rec pr_user_loc_pat ~with_gen env sigma ?loc pat =
  match pat with
  | PUVar (i, gen) -> pr_provenance ~with_gen (Id.print i) gen
  | PUCstr (c, i, f) -> 
      let pc = pr_constructor env c in
        if not (List.is_empty f) then str "(" ++ pc ++ spc () ++ pr_user_pats env sigma f ++ str ")"
	else pc
  | PUInac c -> str "?(" ++ pr_glob_constr_env env sigma c ++ str ")"
  | PUEmpty -> str"!"

and pr_user_pat ?(with_gen=false) env sigma = DAst.with_loc_val (pr_user_loc_pat ~with_gen env sigma)

and pr_user_pats ?(with_gen=true) env sigma pats =
  prlist_with_sep spc (pr_user_pat ~with_gen env sigma) pats

let pr_lhs = pr_user_pats ~with_gen:true

let pplhs lhs =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pp (pr_lhs env sigma lhs)

let pr_body env sigma = function
  | ConstrExpr rhs -> pr_constr_expr ~flags:(Ppconstr.current_flags()) env sigma rhs
  | GlobConstr rhs -> pr_glob_constr_env env sigma rhs
  | Constr c -> str"<constr>"

let rec pr_rhs_aux env sigma = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ Id.print var
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++ pr_body env sigma rhs ++
                            spc () ++ pr_wheres env sigma where
  | Refine (rhs, s) -> spc () ++ str "with" ++ spc () ++
                       prlist_with_sep (fun () -> str",")
                         (pr_constr_expr ~flags:(Ppconstr.current_flags()) env sigma) rhs ++
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env sigma s ++ str "}")

and pr_rhs env sigma = function
  | None -> mt ()
  | Some rhs -> pr_rhs_aux env sigma rhs
and pr_wheres env sigma (l, nts) =
  if List.is_empty l then mt() else
  str"where" ++ spc () ++ prlist_with_sep fnl (pr_where env sigma) l
and pr_where env sigma (sign, eqns) =
  pr_proto env sigma sign ++ str "{" ++ pr_clauses env sigma eqns ++ str "}"
and pr_proto env sigma ((_,id), _, _, l, t, ann) =
  let flags = Ppconstr.current_flags() in
  Id.print id ++ pr_binders ~flags env sigma l ++ pr_opt (fun t -> str" : " ++ pr_constr_expr ~flags env sigma t) t ++
  (match ann with
     None -> mt ()
   | Some (WellFounded (t, rel)) -> str"by wf " ++ pr_constr_expr ~flags env sigma t ++ pr_opt (pr_constr_expr ~flags env sigma) rel
   | Some (Structural id) -> str"by struct " ++ pr_opt (fun x -> pr_id (snd x)) id)

and pr_clause env sigma (Clause (loc, lhs, rhs)) =
  pr_lhs env sigma lhs ++ pr_rhs env sigma rhs

and pr_clauses env sigma =
  prlist_with_sep fnl (pr_clause env sigma)

let pr_user_lhs env sigma lhs =
  let flags = Ppconstr.current_flags() in
  match lhs with
  | SignPats x -> pr_constr_expr ~flags env sigma x
  | RefinePats l -> prlist_with_sep (fun () -> str "|") (pr_constr_expr ~flags env sigma) l

let rec pr_user_rhs_aux env sigma = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ Id.print var
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++
                            pr_body env sigma rhs ++
                            spc () ++ pr_prewheres env sigma where
  | Refine (rhs, s) -> spc () ++ str "with" ++ spc () ++
                       prlist_with_sep (fun () -> str ",")
                         (pr_constr_expr ~flags:(Ppconstr.current_flags()) env sigma) rhs ++
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_user_clauses env sigma s ++ str "}")

and pr_prerhs_aux env sigma = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ Id.print var
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++
                            pr_body env sigma rhs ++
                            spc () ++ pr_prewheres env sigma where
  | Refine (rhs, s) -> spc () ++ str "with" ++ spc () ++
                       prlist_with_sep (fun () -> str ",")
                         (pr_constr_expr ~flags:(Ppconstr.current_flags()) env sigma) rhs ++
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_preclauses env sigma s ++ str "}")

and pr_user_rhs env sigma = pr_opt (pr_user_rhs_aux env sigma)
and pr_prerhs env sigma = pr_opt (pr_prerhs_aux env sigma)

and pr_user_clause env sigma (Pre_equation (lhs, rhs)) =
  pr_user_lhs env sigma lhs ++ pr_user_rhs env sigma rhs

and pr_user_clauses env sigma =
  prlist_with_sep fnl (pr_user_clause env sigma)

and pr_prewheres env sigma (l, nts) =
  if List.is_empty l then mt() else
  str"where" ++ spc () ++ prlist_with_sep fnl (pr_prewhere env sigma) l
and pr_prewhere env sigma (sign, eqns) =
  pr_proto env sigma sign ++ str "{" ++ pr_user_clauses env sigma eqns ++ str "}"

and pr_preclause env sigma (Pre_clause (loc, lhs, rhs)) =
  pr_lhs env sigma lhs ++ pr_prerhs env sigma rhs

and pr_preclauses env sigma =
  prlist_with_sep fnl (pr_preclause env sigma)

let ppclause clause =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pp(pr_clause env sigma clause)

let wit_equations_list : (pre_equation list, Util.Empty.t) GenConstr.tag =
  GenConstr.create "equations_list"

let next_ident_away s ids =
  let n' = Namegen.next_ident_away s !ids in
    ids := Id.Set.add n' !ids; n'

type equation_option = OInd | OEquations | OTactic of Libnames.qualid
    
type equation_user_option = equation_option * bool

type equation_options = equation_user_option list

let pr_r_equation_user_option _prc _prlc _prt l =
  mt ()

let pr_equation_options  _prc _prlc _prt l =
  mt ()

(* Attributes *)

let derive_flags =
  let open Attributes in
  let open Notations in
  Attributes.qualify_attribute "derive" 
    (bool_attribute ~name:"eliminator" ++
     bool_attribute ~name:"equations")
    
let equations_attributes attrs = 
  let open Attributes in
  let add_bool key value l =
    match value with
    | Some b -> (key, b) :: l
    | None -> l
  in
  let (eliminator, equations) = parse derive_flags attrs in
  add_bool OInd eliminator (add_bool OEquations equations [])

let tactic_parser : qualid Attributes.key_parser = fun ?loc orig args ->
  let open Attributes in
  assert_once ?loc ~name:"tactic" orig;
  match args with
  | VernacFlagLeaf (FlagString str) -> qualid_of_string str
  | VernacFlagLeaf (FlagQualid q) -> q
  |  _ -> CErrors.user_err ?loc (Pp.str "Ill formed \"tactic\" attribute")
let equations_tactic =
  Attributes.attribute_of_list ["tactic",tactic_parser]

let equations_obligations =
  Attributes.bool_attribute ~name:"obligations"

type rec_type_item =
  | Guarded of (Id.t * rec_annot) list (* for mutual rec *)
  | Logical of int * Id.t with_loc (* for nested wf rec: number of arguments before the side-condition *)

type rec_type = rec_type_item option list

let is_structural = function Some (Guarded _) :: _ -> true | _ -> false

let has_logical rec_type =
  List.exists (function Some (Logical _) -> true | _ -> false) rec_type

let is_rec_call id c =
  let id' = Constant.label c in
  Id.equal id id'
  
let free_vars_of_constr_expr env sigma fid c =
  let rec aux bdvars l = function
    | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
      let id = qualid_basename qid in
      if Id.List.mem id bdvars then l
      else if Option.cata (Id.equal id) false fid then l
      else
        (try
           match Nametab.locate_extended (Libnames.qualid_of_ident id) with
           | Globnames.TrueGlobal gr ->
             if not (Globnames.isConstructRef gr) then Id.Set.add id l
             else l
           | Globnames.Abbrev _ -> l
         with Not_found -> Id.Set.add id l)
    | { CAst.v = CNotation (_,(InConstrEntry, "?( _ )"), _) } -> l
    | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] Id.Set.empty c

let ids_of_pats env sigma id pats =
  fold_left (fun ids p -> Id.Set.union ids (free_vars_of_constr_expr env sigma id p))
    Id.Set.empty pats

type wf_rec_info =
  Constrexpr.constr_expr * Constrexpr.constr_expr option * Id.t with_loc

type program_rec_info =
  (rec_annot, wf_rec_info) by_annot

type program_info = {
  program_loc : Loc.t option;
  program_id : Id.t;
  program_orig_type : EConstr.t; (* The original type *)
  program_sort : Sorts.t; (* The sort of this type *)
  program_sign : EConstr.rel_context;
  program_arity : EConstr.t;
  program_rec : program_rec_info option;
  program_impls : Impargs.manual_implicits;
  program_implicits : Impargs.implicit_status list;
}

type 'a mutual_fix = MutFix of (program_info * 'a) list * int array * EConstr.rec_declaration

let map_universe f u =
  let u' = f (EConstr.mkSort (EConstr.ESorts.make u)) in
  match Constr.kind (EConstr.Unsafe.to_constr u') with
  | Sort s -> s
  | _ -> assert false

let map_program_info f p =
  { p with
    program_orig_type = f p.program_orig_type;
    program_sort = map_universe f p.program_sort;
    program_sign = Context.Rel.map f p.program_sign;
    program_arity = f p.program_arity }

let _check_linearity env sigma opats =
  let rec aux ids pats = 
    List.fold_left (fun ids pat ->
      DAst.with_loc_val (fun ?loc pat ->
      match pat with
      | PUVar (n, _) ->
	if Id.Set.mem n ids then
          CErrors.user_err ?loc
            (str "Non-linear occurrence of variable in patterns: " ++ pr_user_pats env sigma opats)
	else Id.Set.add n ids
      | PUInac _ -> ids
      | PUEmpty -> ids
      | PUCstr (_, _, pats) -> aux ids pats) pat)
      ids pats
  in ignore (aux Id.Set.empty opats)

let is_implicit_arg = function
  | GImplicitArg _ -> true
  | _ -> false

let pattern_of_glob_constr env sigma avoid patname gc =
  let avoid = ref avoid in
  let rec constructor ?loc c l =
    let ind, _ = c in
    let nparams = Inductiveops.inductive_nparams env ind in
    let nargs = Inductiveops.constructor_nrealargs env c in
    let l =
      if List.length l < nargs then
        user_err_loc (loc, str "Constructor " ++
          Printer.pr_global (GlobRef.ConstructRef c) ++ 
          str" is applied to too few arguments")
      else
        if List.length l = nparams + nargs then
          List.skipn nparams l
        else if List.length l = nargs then l
        else
          user_err_loc (loc, str "Constructor is applied to too many arguments");
    in
    Dumpglob.add_glob ?loc (GlobRef.ConstructRef c);
    PUCstr (c, nparams, List.map (DAst.map_with_loc (aux Anonymous)) l)
  and aux patname ?loc = function
    | GVar id -> PUVar (id, User)
    | GHole k ->
      (match patname with
      | Name id when is_implicit_arg k -> PUVar (id, Implicit)
      | _ -> 
        let id = Id.of_string "wildcard" in
        let n = next_ident_away id avoid in
        PUVar (n, Generated))
    | GRef (GlobRef.ConstructRef cstr,_) -> constructor ?loc cstr []
    | GRef (GlobRef.ConstRef _ as c, _) when Environ.QGlobRef.equal env c (Lazy.force coq_bang) -> PUEmpty
    | GApp (c, l) ->
      begin match DAst.get c with
        | GRef (GlobRef.ConstructRef cstr,_) -> constructor ?loc cstr l
        | GRef (GlobRef.ConstRef _ as c, _) when Environ.QGlobRef.equal env c (Lazy.force coq_inacc) ->
          let inacc = List.hd (List.tl l) in
          PUInac inacc
        | _ ->
          user_err_loc
            (loc,
             str "Cannot interpret " ++ pr_glob_constr_env env sigma c ++ str " as a constructor")
      end
  (* | GLetIn (Name id as na',b,None,e) when is_gvar id e && na = Anonymous ->
   *    (\* A canonical encoding of aliases *\)
   *    DAst.get (cases_pattern_of_glob_constr na' b) *)
    | _ -> user_err_loc (loc, str ("Cannot interpret globalized term as a pattern"))
  in
  let gc =DAst.map_with_loc (aux patname) gc in
  !avoid, gc

let program_type p = EConstr.it_mkProd_or_LetIn p.program_arity p.program_sign

let interp_pat env sigma notations ~avoid p pat =
  (* we push variables with dummy type info for the new bound variables
     (intern doesn't look at the type of the variables) *)
  let vars = (Id.Set.elements avoid) (* (ids_of_pats [p])) *) in
  (* let () = Feedback.msg_debug (str"Variables " ++ prlist_with_sep spc pr_id vars) in *)
  let tys = List.map (fun _ -> EConstr.mkProp) vars in
  let rlv = List.map (fun _ -> EConstr.ERelevance.relevant) vars in
  let impls = List.map (fun _ -> []) vars in
  (* let () = Feedback.msg_debug (str"Internalizing " ++ pr_constr_expr p) in *)
  let ienv = try compute_internalization_env env sigma Variable vars tys impls with Not_found ->
    anomaly (str"Building internalization environment")
  in
  let notations = List.map Metasyntax.prepare_where_notation notations in
  let vars, rlv, tys, ienv =
    match p with
    | Some (p, _) ->
      let ty = program_type p in
      let r = Retyping.relevance_of_type env sigma ty in
      let ienv =
        try compute_internalization_env env sigma ~impls:ienv Recursive [p.program_id] [ty] [p.program_impls]
        with Not_found -> anomaly (str"Building internalization environment")
      in
      (p.program_id :: vars, r :: rlv, ty :: tys, ienv)
    | None -> (vars, rlv, tys, ienv)
  in
  let nctx =
    List.map3 (fun id r ty ->
        Context.Rel.Declaration.LocalAssum
          (Context.make_annot (Name id) (EConstr.Unsafe.to_relevance r),
           EConstr.Unsafe.to_constr ty))
      vars rlv tys
  in
  let env = Environ.push_rel_context nctx env in
  let gc =
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env ienv) notations;
      try Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~impls:ienv env sigma pat
      with Not_found -> anomaly (str"Internalizing pattern")) ()
  in
  try
    match p with
    | Some ({ program_id = id }, patnames) ->
      DAst.with_loc_val (fun ?loc g ->
          let fn, args =
            match g with
            | GApp (fn, args) -> fn, args
            | _ -> DAst.make ?loc g, []
          in
          DAst.with_loc_val (fun ?loc gh ->
              match gh with
              | GVar fid when Id.equal fid id ->
                let rec aux avoid args patnames =
                  match args, patnames with
                  | a :: args, patname :: patnames ->
                    let avoid, pat = pattern_of_glob_constr env sigma avoid patname a in
                    let avoid, pats = aux avoid args patnames in
                    avoid, pat :: pats
                  | a :: args, [] ->
                    let avoid, pat = pattern_of_glob_constr env sigma avoid Anonymous a in
                    let avoid, pats = aux avoid args [] in
                    avoid, pat :: pats
                  | [], _ -> avoid, []
                in aux avoid args patnames
              | _ ->
                user_err_loc (loc,
                              str "Expecting a pattern for " ++ Id.print id))
            fn) gc
    | None -> let avoid, pat = pattern_of_glob_constr env sigma avoid Anonymous gc in
      avoid, [pat]
  with Not_found -> anomaly (str"While translating pattern to glob constr")

(* let rename_away_from ids pats =
  let rec aux ?loc pat =
    match pat with
    | PUVar (id, true) when Id.Set.mem id !ids ->
      let id' = next_ident_away id ids in
      PUVar (id', true)
    | PUVar (id, _) -> pat
    | PUCstr (c, n, args) -> PUCstr (c, n, List.map (DAst.map_with_loc aux) args)
    | PUInac c -> pat
    | PUEmpty -> pat
  in
  List.map (DAst.map_with_loc aux) pats *)

let interleave_implicits impls pats =
  let rec aux impls pats =
    match impls, pats with
    | Some id :: impls, pats -> DAst.make (PUVar (id, Implicit)) :: aux impls pats
    | None :: impls, pat :: pats -> pat :: aux impls pats
    | None :: _, [] -> []
    | [], pats -> pats
  in aux impls pats

let interp_eqn env sigma notations p ~avoid eqn =
  let whereid = ref (Nameops.add_suffix p.program_id "_abs_where") in
  let patnames =
    List.rev_map (fun decl -> Context.Rel.Declaration.get_name decl) p.program_sign
  in
  let impls =
    List.map (fun a ->
        if Impargs.is_status_implicit a then Some (Impargs.name_of_implicit a) else None)
      p.program_implicits
  in
  let interp_pat notations avoid = interp_pat env sigma notations ~avoid in
  let rec aux notations avoid curpats (Pre_equation (pat, rhs)) =
    let loc, avoid, pats =
      match pat with
      | SignPats pat ->
        let avoid = Id.Set.union avoid (ids_of_pats env sigma (Some p.program_id) [pat]) in
        let loc = Constrexpr_ops.constr_loc pat in
        let avoid, pats = interp_pat notations avoid (Some (p, patnames)) pat in
        loc, avoid, pats
      | RefinePats pats ->
        let patids = ids_of_pats env sigma None pats in
        (* let curpats = rename_away_from patids curpats in *)
        let avoid = Id.Set.union avoid patids in
        let loc = Constrexpr_ops.constr_loc (List.hd pats) in
        let avoid, pats = List.fold_left_map (fun avoid -> interp_pat notations avoid None) avoid pats in
        let pats = List.map (fun x -> List.hd x) pats in
        let pats =
          (* At the toplevel only, interleave using the implicit
             status of the function arguments *)
          if curpats = [] then interleave_implicits impls pats
          else curpats @ pats in
        loc, avoid, pats
    in
    Pre_clause (loc, pats, Option.map (interp_rhs notations avoid pats) rhs)
  and aux2 notations avoid (Pre_equation (pat, rhs)) =
    Pre_equation (pat, Option.map (interp_rhs' notations avoid) rhs)
  and interp_rhs' notations avoid = function
    | Refine (c, eqs) ->
      let avoid = Id.Set.union avoid (ids_of_pats env sigma None c) in
      let interp c =
        let wheres, c = CAst.with_loc_val (interp_constr_expr notations avoid) c in
        if not (List.is_empty wheres) then
          user_err_loc (Constrexpr_ops.constr_loc c,
                        str"Pattern-matching lambdas not allowed in refine");
        c
      in
      Refine (List.map interp c, map (aux2 notations avoid) eqs)
    | Program (c, (w, nts)) ->
       let notations = nts @ notations in
       let w = interp_wheres avoid w notations in
       let w', c =
         match c with
         | ConstrExpr c ->
            let wheres, c = CAst.with_loc_val (interp_constr_expr notations avoid) c in
            wheres, ConstrExpr c
         | GlobConstr c -> [], GlobConstr c
         | Constr c -> [], Constr c
       in
       Program (c, (List.append w' w, nts))
    | Empty i -> Empty i
  and interp_rhs notations avoid curpats = function
    | Refine (c, eqs) ->
      let avoid = Id.Set.union avoid (ids_of_pats env sigma None c) in
      let interp c =
        let wheres, c = CAst.with_loc_val (interp_constr_expr notations avoid) c in
        if not (List.is_empty wheres) then
          user_err_loc (Constrexpr_ops.constr_loc c,
                        str"Pattern-matching lambdas not allowed in refine");
        c
      in
      Refine (List.map interp c, map (aux notations avoid curpats) eqs)
    | Program (c, (w, nts)) ->
       let w = interp_wheres avoid w (nts @ notations) in
       let w', c =
         match c with
         | ConstrExpr c ->
            let wheres, c = CAst.with_loc_val (interp_constr_expr notations avoid) c in
            wheres, ConstrExpr c
         | GlobConstr c -> [], GlobConstr c
         | Constr c -> [], Constr c
       in
       Program (c, (List.append w' w, nts))
    | Empty i -> Empty i
  and interp_wheres avoid w notations =
    let interp_where (((loc,id),decl,nested,b,t,reca) as p,eqns) =
      Dumpglob.dump_reference ?loc "<>" (Id.to_string id) "def";
      p, map (aux2 notations avoid) eqns
    in List.map interp_where w
  and interp_constr_expr notations (avoid : Id.Set.t) ?loc c =
    let wheres = ref [] in
    let rec aux' avoid ?loc c =
      match c with
      (* | CApp ((None, { CAst.v = CRef (qid', ie) }), args)
       *      when qualid_is_ident qid' && Id.equal (qualid_basename qid') p.program_id ->
       *    let id' = qualid_basename qid' in
       *    (match p.program_rec with
       *     | None | Some (Structural _) -> CAst.make ~loc c
       *     | Some (WellFounded (_, _, r)) ->
       *       let args =
       *         List.map (fun (c, expl) -> CAst.with_loc_val (aux' ids) c, expl) args in
       *       let c = CApp ((None, CAst.(make ~loc (CRef (qid', ie)))), args) in
       *       let arg = CAst.make ~loc (CApp ((None, CAst.make ~loc c), [chole id' loc])) in
       *       arg) *)
      | CGenarg (Raw (tag, eqns)) when Option.has_some (GenConstr.eq tag wit_equations_list) ->
        let Refl = Option.get @@ GenConstr.eq tag wit_equations_list in
        let id = !whereid in
        let () = whereid := Nameops.increment_subscript id in
        let avoid = Id.Set.add id avoid in
        let eqns = List.map (aux2 notations avoid) eqns in
        let () =
          wheres := (((loc, id), None, None, [], None, None), eqns) :: !wheres;
        in Constrexpr_ops.mkIdentC id
      | _ -> map_constr_expr_with_binders Id.Set.add
             (fun avoid -> CAst.with_loc_val (aux' avoid)) avoid (CAst.make ?loc c)
    in
    let c' = aux' avoid ?loc c in
    !wheres, c'
  in aux notations avoid [] eqn

let is_recursive i : pre_equation wheres -> bool = fun eqs ->
  let rec occur_eqn (Pre_equation (_, rhs)) =
    match rhs with
    | Some (Program (c,w)) ->
      (match c with
      | ConstrExpr c -> occur_var_constr_expr i c || occurs w
      | GlobConstr c -> occurs w
      | Constr _ -> occurs w)
    | Some (Refine (c, eqs)) ->
       List.exists (occur_var_constr_expr i) c || occur_eqns eqs
    | _ -> false
  and occur_eqns eqs = List.exists occur_eqn eqs
  and occurs_notations nts =
    List.exists (fun nt -> occur_var_constr_expr i nt.Vernacexpr.ntn_decl_interp) nts
  and occurs eqs =
    List.exists (fun (_,eqs) -> occur_eqns eqs) (fst eqs) || occurs_notations (snd eqs)
  in occurs eqs
