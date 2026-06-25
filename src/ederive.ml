(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr

type derive_fn_ty = pm:Declare.OblState.t -> poly:PolyFlags.t -> Names.GlobRef.t -> Declare.OblState.t

type derive_record =
  { derive_name : string;
    derive_fn : derive_fn_ty }

let make_derive fn ~pm ~poly s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global ~rigid:Evd.univ_rigid env sigma s in
  fn ~pm env sigma ~poly c

let make_derive_ind fn ~pm ~poly s =
  let fn ~pm env sigma ~poly c =
    match EConstr.kind sigma c with
    | Ind (i,u) -> fn ~pm env sigma ~poly (i,u)
    | _ -> CErrors.user_err (Pp.str"Expected an inductive type")
  in make_derive fn ~pm ~poly s

let table = ref (CString.Map.empty : derive_fn_ty CString.Map.t)

let register_derive d =
  table := CString.Map.add d.derive_name d.derive_fn !table

let get_derive d =
  try CString.Map.find d !table
  with Not_found -> CErrors.user_err Pp.(str"No derive declared for " ++ str d)

module StringOrd = struct type t = string let compare = String.compare end
module StringSet = Set.Make(StringOrd)

(** We keep a table of which derives have been performed yet for a given global reference. *)
type derive_instance = (string * Names.GlobRef.t)

type derive_instance_map = StringSet.t Environ.QGlobRef.Map.t

let derived_instances : derive_instance_map ref = Summary.ref Environ.QGlobRef.Map.empty ~name:"derived-instances"

let cache_instance (derive, gr) =
  let grderives = 
    match Environ.QGlobRef.Map.find_opt (Global.env ()) gr !derived_instances with
    | Some s -> s
    | None -> StringSet.empty
  in
  derived_instances := Environ.QGlobRef.Map.add (Global.env ()) gr (StringSet.add derive grderives) !derived_instances

let subst_instance (subst, (derive, gr)) =
  (derive, fst (Globnames.subst_global subst gr))

let discharge_instance (derive, gr as o) =
  if Globnames.isVarRef gr then None
  else Some o

let derive_instance_input : derive_instance -> Libobject.obj =
  let decl = 
    Libobject.superglobal_object "derive instances state"
      ~cache:cache_instance
      ~discharge:discharge_instance
      ~subst:(Some subst_instance)
  in 
  Libobject.declare_object decl

let register_instance decl =
  Lib.add_leaf (derive_instance_input decl)

let check_derive s gr =
  try
    let grds = Environ.QGlobRef.Map.find (Global.env ()) gr !derived_instances in
    StringSet.mem s grds
  with Not_found -> false

let derive_one ~pm poly d grs =
  let fn = get_derive d in
  List.fold_left (fun pm x ->
      let pm = fn ~pm ~poly x in
      register_instance (d, x);
      pm) pm grs

let derive ~pm ~poly ds grs =
  let grs = List.map (fun (loc, gr) -> Dumpglob.add_glob ?loc gr; gr) grs in
  List.fold_left (fun pm d -> derive_one ~pm poly d grs) pm ds
