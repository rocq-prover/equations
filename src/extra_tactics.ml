open Locusops
open Constr
open Names
open Tactics
open Equations_common
open EConstr

let decompose_app h h' c =
  Proofview.Goal.enter begin fun gl ->
    let f, args = EConstr.decompose_app (Proofview.Goal.sigma gl) c in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let fty = Retyping.get_type_of env sigma f in
    let fty = Reductionops.whd_all env sigma fty in
    let flam = mkLambda (EConstr.nameR (Id.of_string "f"), fty, mkApp (mkRel 1, args)) in
      (Proofview.tclTHEN (letin_tac None (Name h) f None allHyps)
         (letin_tac None (Name h') flam None allHyps)) end

let autounfold_ref gr =
  let db = match gr with
    | GlobRef.ConstRef c -> Names.Id.to_string (Names.Constant.label c)
    | _ -> assert false
  in Eauto.autounfold ["core";db] Locusops.onConcl


(** [intro_binder_name] introduces the next hypothesis reusing the binder
    name verbatim (only appending subscripts in case of clash), instead of
    going through fresh name generation which would mangle it under
    [Mangle Names]. It is meant to reintroduce hypotheses whose binder names
    are user-given, e.g. after [revert]. Falls back to [intro] on anonymous
    binders. *)
let intro_binder_name =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let name =
      match kind sigma concl with
      | Prod (na, _, _) | LetIn (na, _, _, _) -> na.Context.binder_name
      | _ -> Anonymous
    in
    match name with
    | Anonymous -> Tactics.intro
    | Name id ->
      let avoid = List.fold_left (fun avoid decl ->
          Id.Set.add (Context.Named.Declaration.get_id decl) avoid)
          Id.Set.empty (Proofview.Goal.hyps gl)
      in
      let rec freshen id =
        if Id.Set.mem id avoid then freshen (Nameops.increment_subscript id) else id
      in
      Tactics.intro_mustbe_force (freshen id)
  end

open Proofview.Goal
open Proofview.Notations

(** [refine_ho c]

  Matches a lemma [c] of type [∀ ctx, ty] with a conclusion of the form
  [∀ ctx, ?P args] using second-order matching on the problem
  [ctx |- ?P args = ty] and then refines the goal with [c]. *)

let refine_ho c =
  enter begin fun gl ->
    let env = env gl in
    let sigma = sigma gl in
    let concl = concl gl in
    let ty = Retyping.get_type_of env sigma c in
    let ts = TransparentState.full in
    let flags = Evarconv.default_flags_of ts in
    let evd = ref (to_evar_map sigma) in
    let rec aux env concl ty =
      match kind sigma concl, kind sigma ty with
      | Prod (na, b, t), Prod (na', b', t') ->
         (match Evarconv.unify_delay ~flags env !evd b b' with
          | exception Evarconv.UnableToUnify _ -> error "Products do not match"
          | evm -> evd := evm;
                        aux (push_rel (of_tuple (na,None,b)) env) t t')
      (* | _, LetIn (na, b, _, t') -> *)
      (*    aux env t (subst1 b t') *)
      | _, App (ev, args) when isEvar sigma ev ->
         let (evk, subst as ev) = destEvar sigma ev in
         let sigma = !evd in
         let sigma,ev = evar_absorb_arguments env sigma ev (Array.to_list args) in
         let evargs = Evd.expand_existential sigma ev in
         let argtest = Evarconv.default_occurrence_test ~allowed_evars:Evarsolve.AllowedEvars.all ts in
         let argoccs = List.map
             (fun _ -> Evarconv.Unspecified Evd.Abstraction.Abstract) evargs in
         let sigma, b = Evarconv.second_order_matching flags env sigma ev (argtest,argoccs) concl in
         if not b then
           error "Second-order matching failed"
         else Proofview.Unsafe.tclEVARS sigma <*>
                Refine.refine ~typecheck:false (fun sigma -> (sigma, c))
      | _, _ -> error "Couldn't find a second-order pattern to match"
    in aux env concl ty end
